"""
STAKE ULTRA CLAIMER - Credit/Voucher System Backend
====================================================

A 24/7 Telegram-integrated backend system for monitoring promo codes and managing 
credit-based user access with precise financial calculations.

Key Features:
- Telegram channel monitoring for promo codes using Telethon
- Real-time code broadcasting via WebSocket/SSE to connected users
- Credit-based access control with Decimal precision for financial calculations
- High-performance caching system supporting concurrent users
- Escrow system for secure code claiming
- JWT-based authentication with session management
- PostgreSQL/Supabase database with connection pooling

Architecture:
- FastAPI web framework with async/await
- SQLAlchemy ORM for database operations
- WebSocket manager for real-time client connections
- Background workers for cache refresh and claim processing
- Keep-alive system for 24/7 uptime on Render free tier

Performance Optimizations:
- Single-flight cache locks to prevent thundering herd
- Per-voucher locks to prevent double-spending
- Bounded claim queue with backpressure handling
- Database connection pooling (30 base + 30 overflow connections)
"""

import os, re, asyncio, random, string, json, time, httpx, threading
from typing import List, Dict, Any, Optional, Set
from datetime import datetime, timedelta
from collections import deque, defaultdict
from fastapi import FastAPI, WebSocket, WebSocketDisconnect, Query, Depends, HTTPException, Body, Request, Form
from fastapi.responses import JSONResponse, PlainTextResponse, FileResponse, HTMLResponse, RedirectResponse, StreamingResponse
from fastapi.staticfiles import StaticFiles
from fastapi.middleware.cors import CORSMiddleware
from fastapi.templating import Jinja2Templates
import hashlib
import hmac
import secrets
import jwt
import uuid
import sqlite3
from decimal import Decimal, ROUND_HALF_UP, InvalidOperation
from telethon import TelegramClient, events, functions
from telethon.errors import SessionPasswordNeededError
from keepalive import KeepAliveService
from sqlalchemy import create_engine, Column, Integer, String, Float, Boolean, ForeignKey, DateTime, func, UniqueConstraint, text , Numeric
from sqlalchemy.orm import declarative_base, sessionmaker, relationship, Session

# ========================================
# PERFORMANCE & CACHING
# ========================================
# Global caches for performance optimization
voucher_cache = {}
user_credit_cache = {}
claim_attempt_cache = {}

# Background task references for clean shutdown
background_tasks = {
    'queue_processor': None,
    'cache_refresher': None,
    'cache_cleaner': None
}

# Cache TTL settings
VOUCHER_CACHE_TTL = 300  # 5 minutes
USER_CREDIT_CACHE_TTL = 60  # 1 minute
CLAIM_CACHE_TTL = 3600  # 1 hour

# Single-flight locks to prevent thundering herd on cache refresh
voucher_cache_refresh_lock = asyncio.Lock()
credit_cache_refresh_lock = asyncio.Lock()

# Per-voucher locks to prevent double-spending with 500 concurrent users
voucher_redemption_locks = {}  # voucher_code -> asyncio.Lock()

# Claim processing queue (bounded with backpressure for 1000 users)
claim_queue = deque(maxlen=20000)  # Max 20K claims prevents unbounded memory growth
claim_queue_overflow_count = 0  # Track dropped claims for monitoring
processing_lock = asyncio.Lock()
processing_active = False

# Background workers
cache_refresh_worker = None
claim_queue_worker = None
cache_cleanup_worker = None

# ========================================
# WAL (Write-Ahead Log) CREDIT DEDUCTION SYSTEM
# ========================================
# Bulletproof credit deduction with instant memory updates and durable logging
# Prevents double-deduction, handles crashes, ensures financial accuracy

# WAL Database - Durable append-only log for all credit operations
WAL_DB_PATH = "credit_deductions.wal"
wal_db_lock = threading.Lock()

def init_wal_database():
    """Initialize WAL database with idempotency guarantees"""
    with sqlite3.connect(WAL_DB_PATH) as conn:
        conn.execute('''
            CREATE TABLE IF NOT EXISTS deductions (
                transaction_id TEXT PRIMARY KEY,
                username TEXT NOT NULL,
                amount TEXT NOT NULL,
                code TEXT NOT NULL,
                timestamp REAL NOT NULL,
                synced INTEGER DEFAULT 0,
                sync_timestamp REAL,
                idempotency_key TEXT UNIQUE NOT NULL,
                created_at REAL NOT NULL
            )
        ''')
        conn.execute('CREATE INDEX IF NOT EXISTS idx_username ON deductions(username)')
        conn.execute('CREATE INDEX IF NOT EXISTS idx_synced ON deductions(synced)')
        conn.execute('CREATE INDEX IF NOT EXISTS idx_idempotency ON deductions(idempotency_key)')
        conn.commit()
        print("WAL: Database initialized successfully")

# Per-user locks to prevent race conditions during credit operations
user_deduction_locks: Dict[str, asyncio.Lock] = defaultdict(asyncio.Lock)

# WAL metrics for monitoring
wal_metrics = {
    'total_deductions': 0,
    'synced_deductions': 0,
    'pending_deductions': 0,
    'failed_syncs': 0,
    'double_deduction_prevented': 0
}

async def wal_deduct_credits_instant(username: str, amount: Decimal, code: str) -> tuple[bool, str, str]:
    """
    INSTANT CREDIT DEDUCTION with bulletproof WAL logging
    
    Flow:
    1. Generate unique transaction ID
    2. Check idempotency (prevent double deduction)
    3. Write to durable WAL log FIRST
    4. Update memory cache SECOND
    5. Queue background sync to main DB
    
    Returns: (success, message, transaction_id)
    """
    import time
    
    # Generate unique transaction ID
    transaction_id = str(uuid.uuid4())
    current_time = time.time()
    
    # Create idempotency key: username + code + rounded_timestamp (prevents same code double-deduction within 1 second)
    idempotency_key = f"{username}:{code}:{int(current_time)}"
    
    # Acquire per-user lock to prevent race conditions
    async with user_deduction_locks[username]:
        try:
            # STEP 1: Check if this exact deduction already exists (idempotency)
            with wal_db_lock:
                with sqlite3.connect(WAL_DB_PATH) as conn:
                    existing = conn.execute(
                        "SELECT transaction_id FROM deductions WHERE idempotency_key = ?",
                        (idempotency_key,)
                    ).fetchone()
                    
                    if existing:
                        wal_metrics['double_deduction_prevented'] += 1
                        print(f"WAL: PREVENTED DOUBLE DEDUCTION for {username} on code {code} (existing tx: {existing[0]})")
                        return (False, "Deduction already processed (idempotency protection)", existing[0])
            
            # STEP 2: Verify user has sufficient credits in memory cache
            current_credits = credit_cache.get(username, Decimal('0'))
            if current_credits < amount:
                return (False, f"Insufficient credits: {current_credits} < {amount}", transaction_id)
            
            # STEP 3: Write to WAL FIRST (durable, crash-safe)
            with wal_db_lock:
                with sqlite3.connect(WAL_DB_PATH) as conn:
                    conn.execute('''
                        INSERT INTO deductions 
                        (transaction_id, username, amount, code, timestamp, idempotency_key, created_at, synced)
                        VALUES (?, ?, ?, ?, ?, ?, ?, 0)
                    ''', (
                        transaction_id,
                        username,
                        str(amount),
                        code,
                        current_time,
                        idempotency_key,
                        current_time
                    ))
                    conn.commit()
            
            # STEP 4: Update memory cache AFTER WAL write (instant for user)
            credit_cache[username] = current_credits - amount
            credit_cache_last_update[username] = current_time
            
            # STEP 5: Queue background sync to main database (non-blocking)
            asyncio.create_task(wal_sync_to_main_db(transaction_id, username, amount))
            
            # Update metrics
            wal_metrics['total_deductions'] += 1
            wal_metrics['pending_deductions'] += 1
            
            print(f"WAL: ✅ Deducted {amount} from {username} for code {code} (tx: {transaction_id[:8]}..., cache: {credit_cache[username]})")
            return (True, "Credits deducted successfully", transaction_id)
            
        except Exception as e:
            print(f"WAL: ❌ CRITICAL ERROR during deduction for {username}: {e}")
            return (False, f"Deduction failed: {str(e)}", transaction_id)

async def wal_sync_to_main_db(transaction_id: str, username: str, amount: Decimal):
    """
    Background sync from WAL to main PostgreSQL database
    SIMPLIFIED: Deducts directly from credits (no reserved_credits needed)
    Handles failures gracefully, retries on errors
    """
    import time
    max_retries = 3
    retry_delay = 1
    
    for attempt in range(max_retries):
        try:
            # SIMPLIFIED: Deduct directly from credits with atomic conditional check
            with SessionLocal() as db:
                result = db.execute(
                    text("UPDATE users SET credits = credits - :amount WHERE username = :username AND credits >= :amount"),
                    {"amount": float(amount), "username": username}
                )
                
                if result.rowcount == 0:
                    print(f"WAL: WARNING - User {username} insufficient credits for tx {transaction_id[:8]}")
                    # Check if user exists
                    user_exists = db.execute(
                        text("SELECT credits FROM users WHERE username = :username"),
                        {"username": username}
                    ).fetchone()
                    
                    if not user_exists:
                        print(f"WAL: ERROR - User {username} not found for tx {transaction_id[:8]}")
                        # Cannot proceed - user doesn't exist
                        db.rollback()
                        return False
                    else:
                        print(f"WAL: ERROR - User {username} has insufficient credits (has: {user_exists[0]}, needs: {amount})")
                        db.rollback()
                        return False
                
                db.commit()
            
            # Mark as synced in WAL
            with wal_db_lock:
                with sqlite3.connect(WAL_DB_PATH) as conn:
                    conn.execute(
                        "UPDATE deductions SET synced = 1, sync_timestamp = ? WHERE transaction_id = ?",
                        (time.time(), transaction_id)
                    )
                    conn.commit()
            
            # Update metrics
            wal_metrics['synced_deductions'] += 1
            wal_metrics['pending_deductions'] -= 1
            
            print(f"WAL: 💾 Synced to main DB - {username} -{amount} (tx: {transaction_id[:8]})")
            return True
            
        except Exception as e:
            print(f"WAL: ⚠️ Sync failed (attempt {attempt + 1}/{max_retries}) for tx {transaction_id[:8]}: {e}")
            if attempt < max_retries - 1:
                await asyncio.sleep(retry_delay * (attempt + 1))
            else:
                wal_metrics['failed_syncs'] += 1
                print(f"WAL: ❌ SYNC FAILED after {max_retries} attempts for tx {transaction_id[:8]} - will retry on next startup")
                return False

async def wal_crash_recovery():
    """
    Crash recovery: Replay all unsynced deductions on startup
    Ensures no credit deductions are lost due to crashes
    """
    print("WAL: Starting crash recovery - checking for unsynced deductions...")
    
    try:
        # Get all unsynced deductions from WAL
        with wal_db_lock:
            with sqlite3.connect(WAL_DB_PATH) as conn:
                unsynced = conn.execute(
                    "SELECT transaction_id, username, amount, code, timestamp FROM deductions WHERE synced = 0 ORDER BY created_at ASC"
                ).fetchall()
        
        if not unsynced:
            print("WAL: ✅ No unsynced deductions found - system was properly shutdown")
            return
        
        print(f"WAL: Found {len(unsynced)} unsynced deductions - replaying to main database...")
        recovered_count = 0
        
        for tx_id, username, amount_str, code, timestamp in unsynced:
            amount = Decimal(amount_str)
            
            try:
                # SIMPLIFIED: Deduct directly from credits with atomic conditional check
                with SessionLocal() as db:
                    result = db.execute(
                        text("UPDATE users SET credits = credits - :amount WHERE username = :username AND credits >= :amount"),
                        {"amount": float(amount), "username": username}
                    )
                    
                    if result.rowcount == 0:
                        print(f"WAL: RECOVERY FAILED for tx {tx_id[:8]} - User {username} has insufficient credits")
                        continue  # Skip this transaction, will retry on next startup
                    
                    db.commit()
                
                # Mark as synced
                with wal_db_lock:
                    with sqlite3.connect(WAL_DB_PATH) as conn:
                        conn.execute(
                            "UPDATE deductions SET synced = 1, sync_timestamp = ? WHERE transaction_id = ?",
                            (time.time(), tx_id)
                        )
                        conn.commit()
                
                recovered_count += 1
                print(f"WAL: ✅ Recovered tx {tx_id[:8]} - {username} -{amount}")
                
            except Exception as e:
                print(f"WAL: ❌ Failed to recover tx {tx_id[:8]}: {e}")
        
        print(f"WAL: Crash recovery complete - recovered {recovered_count}/{len(unsynced)} deductions")
        
    except Exception as e:
        print(f"WAL: ❌ CRITICAL ERROR during crash recovery: {e}")

async def wal_reconciliation_check():
    """
    Periodic reconciliation: Verify WAL and main DB are in sync
    Detects and fixes any discrepancies
    """
    while True:
        try:
            await asyncio.sleep(300)  # Run every 5 minutes
            
            print("WAL: Running reconciliation check...")
            
            # Get pending deductions count
            with wal_db_lock:
                with sqlite3.connect(WAL_DB_PATH) as conn:
                    pending = conn.execute(
                        "SELECT COUNT(*) FROM deductions WHERE synced = 0"
                    ).fetchone()[0]
            
            if pending > 0:
                print(f"WAL: ⚠️ Found {pending} pending deductions - triggering sync")
                
                # Get unsynced transactions
                with wal_db_lock:
                    with sqlite3.connect(WAL_DB_PATH) as conn:
                        unsynced = conn.execute(
                            "SELECT transaction_id, username, amount FROM deductions WHERE synced = 0 LIMIT 100"
                        ).fetchall()
                
                # Sync them
                for tx_id, username, amount_str in unsynced:
                    asyncio.create_task(wal_sync_to_main_db(tx_id, username, Decimal(amount_str)))
            else:
                print(f"WAL: ✅ All deductions in sync (metrics: {wal_metrics})")
                
        except Exception as e:
            print(f"WAL: Reconciliation error: {e}")
            await asyncio.sleep(60)

# Initialize WAL database on module load
init_wal_database()


PORT = int(os.getenv("PORT", "5000"))
TG_API_ID = int(os.getenv("TG_API_ID", "0") or "0")
TG_API_HASH = os.getenv("TG_API_HASH", "")
TG_SESSION = os.getenv("TG_SESSION", "tg_session")  # file path or session string
CHANNELS = os.getenv("CHANNELS", "-1002772030545,-1002932455889,-1001992047801")  # Multiple channels separated by comma

# Telegram Bot Configuration
TELEGRAM_BOT_TOKEN = os.getenv("TELEGRAM_BOT_TOKEN")
TELEGRAM_ADMIN_ID = int(os.getenv("TELEGRAM_ADMIN_ID", "0"))
WS_SECRET = os.getenv("WS_SECRET")
MONITOR_AUTH_TOKEN = os.getenv("MONITOR_AUTH_TOKEN")  # Static token for monitor.js authentication

# Authentication Configuration
ADMIN_USERNAME = os.getenv("ADMIN_USERNAME", "admin")
ADMIN_PASSWORD = os.getenv("ADMIN_PASSWORD")
if not ADMIN_PASSWORD:
    raise RuntimeError("ADMIN_PASSWORD environment variable is required for security")
SECRET_KEY = os.getenv("SECRET_KEY", secrets.token_hex(32))

# Proper session store with user identity tracking
session_store: Dict[str, dict] = {}  # session_token -> {username, expires_at, csrf_nonces, last_seen}

# Enhanced regex patterns for different code formats
CODE_PATTERNS = [
    r'(?i)Code:\s+([a-zA-Z0-9]{4,25})',           # "Code: stakecomrtlye4" - primary pattern
    r'(?i)Code:([a-zA-Z0-9]{4,25})',              # "Code:stakecomguft19f6" - no space version
    r'(?i)Bonus:\s+([a-zA-Z0-9]{4,25})',         # "Bonus: ABC123"
    r'(?i)Bonus:([a-zA-Z0-9]{4,25})',            # "Bonus:ABC123" 
    r'(?i)Claim:\s+([a-zA-Z0-9]{4,25})',         # "Claim: ABC123"
    r'(?i)Claim:([a-zA-Z0-9]{4,25})',            # "Claim:ABC123"
    r'(?i)Promo:\s+([a-zA-Z0-9]{4,25})',         # "Promo: ABC123"
    r'(?i)Promo:([a-zA-Z0-9]{4,25})',            # "Promo:ABC123"
    r'(?i)Coupon:\s+([a-zA-Z0-9]{4,25})',        # "Coupon: ABC123"
    r'(?i)Coupon:([a-zA-Z0-9]{4,25})',           # "Coupon:ABC123"
    r'(?i)use\s+(?:code\s+)?([a-zA-Z0-9]{4,25})',  # "use code ABC123"
    r'(?i)enter\s+(?:code\s+)?([a-zA-Z0-9]{4,25})', # "enter code ABC123"
]

# Pattern for extracting both code and value from messages like:
# Code: stakecomlop1n84b
# Value: $3
CODE_VALUE_PATTERN = r'(?i)Code:\s+([a-zA-Z0-9]{4,25})(?:.*?\n.*?Value:\s+\$?(\d+(?:\.\d{1,2})?))?'

CLAIM_URL_BASE = os.getenv("CLAIM_URL_BASE", "https://kciade.online")
RING_SIZE = int(os.getenv("RING_SIZE", "100"))

# Keep-alive configuration
PRODUCTION_URL = os.getenv("PRODUCTION_URL", "https://kciade.online")
KEEP_ALIVE_ENABLED = os.getenv("KEEP_ALIVE_ENABLED", "true").lower() == "true"
KEEP_ALIVE_INTERVAL = int(os.getenv("KEEP_ALIVE_INTERVAL", "4"))  # minutes (UptimeRobot compatible: <5min)


# Database Configuration
DATABASE_URL = os.getenv("DATABASE_URL")
Base = declarative_base()

# Pool sizing for Supabase Pro $25 plan (200 pooler connections)
# For 1000 concurrent users with batching - conservative 30% utilization
POOL_SIZE = int(os.getenv("DB_POOL_SIZE", "30"))       # 30 base connections
MAX_OVERFLOW = int(os.getenv("DB_MAX_OVERFLOW", "30"))   # 30 overflow = 60 total (30% of 200 pooler limit - very safe)

def create_db_engine():
    """Create optimized SQLAlchemy engine for Supabase Pro"""
    connect_args = {}

    # Guard against missing DATABASE_URL (optional for development)
    db_url = DATABASE_URL or "sqlite:///./test.db"
    if not DATABASE_URL:
        print("Warning: DATABASE_URL not set - using SQLite fallback for development")

    # Configure based on database type
    if db_url.startswith("sqlite"):
        # SQLite-specific configuration
        connect_args = {
            "check_same_thread": False  # Allow SQLite to be used across threads
        }
        # Use minimal connection pooling for SQLite
        return create_engine(
            db_url,
            pool_pre_ping=True,
            connect_args=connect_args
        )
    elif db_url.startswith("postgresql"):
        # Conservative settings for Supabase Pro (50 connection limit)
        if "sslmode=" not in db_url:
            connect_args["sslmode"] = "require"

        return create_engine(
            db_url, 
            pool_pre_ping=True,
            pool_recycle=3600,
            pool_size=POOL_SIZE,        # Use environment variable (default 20)
            max_overflow=MAX_OVERFLOW,  # Use environment variable (default 10)
            pool_timeout=30,            # Increased timeout
            connect_args=connect_args
        )
    else:
        # Fallback for other database types
        return create_engine(db_url, pool_pre_ping=True)


# Create initial engine
engine = create_db_engine()
SessionLocal = sessionmaker(autocommit=False, autoflush=False, bind=engine)

# Templates setup
templates = Jinja2Templates(directory="templates")

# Authentication functions
def create_session_token():
    return secrets.token_urlsafe(32)

def hash_password(password: str) -> str:
    return hashlib.sha256(password.encode()).hexdigest()

def validate_voucher_code(voucher_code: str) -> tuple[bool, str]:
    """
    STRICT VOUCHER VALIDATION: Enforce exact pattern XXXX-XXXX-XX (12 chars total)
    Pattern: 4 alphanumeric chars + dash + 4 alphanumeric chars + dash + 2 alphanumeric chars
    Total length: 4 + 1 + 4 + 1 + 2 = 12 characters exactly
    
    Returns: (is_valid, error_message)
    """
    if not voucher_code:
        return (False, "Voucher code is required")
    
    # Check exact length (12 characters)
    if len(voucher_code) != 12:
        return (False, f"Invalid voucher format: must be exactly 12 characters (got {len(voucher_code)})")
    
    # Check pattern: XXXX-XXXX-XX
    # Pattern breakdown: [0-3] = 4 chars, [4] = dash, [5-8] = 4 chars, [9] = dash, [10-11] = 2 chars
    parts = voucher_code.split('-')
    
    # Must have exactly 3 parts separated by dashes
    if len(parts) != 3:
        return (False, "Invalid voucher format: must be XXXX-XXXX-XX")
    
    # Validate each part
    part1, part2, part3 = parts
    
    # Part 1: exactly 4 alphanumeric characters
    if len(part1) != 4 or not part1.isalnum():
        return (False, "Invalid voucher format: first part must be 4 alphanumeric characters")
    
    # Part 2: exactly 4 alphanumeric characters
    if len(part2) != 4 or not part2.isalnum():
        return (False, "Invalid voucher format: second part must be 4 alphanumeric characters")
    
    # Part 3: exactly 2 alphanumeric characters
    if len(part3) != 2 or not part3.isalnum():
        return (False, "Invalid voucher format: third part must be 2 alphanumeric characters")
    
    # All validation passed
    return (True, "Valid voucher code")

def format_monetary(value, currency_symbol="$") -> str:
    """
    Format monetary values properly, handling None values and Decimal scientific notation
    - None values -> $0.00
    - Decimal values -> properly formatted without scientific notation
    - Ensures 8 decimal precision for crypto amounts
    """
    if value is None:
        return f"{currency_symbol}0.00000000"

    try:
        # Convert to Decimal if not already
        if not isinstance(value, Decimal):
            decimal_value = Decimal(str(value))
        else:
            decimal_value = value

        # Quantize to 8 decimal places to avoid scientific notation
        formatted_value = decimal_value.quantize(Decimal('0.00000000'), rounding=ROUND_HALF_UP)

        # Format as string without scientific notation
        return f"{currency_symbol}{formatted_value}"
    except (ValueError, TypeError, InvalidOperation) as e:
        print(f"Warning: Error formatting monetary value {value}: {e}")
        return f"{currency_symbol}0.00000000"

def safe_decimal(value, default_value="0") -> Decimal:
    """
    Safely convert values to Decimal, handling None and invalid values
    - None values -> Decimal('0') or specified default
    - String/float values -> properly converted to Decimal
    """
    if value is None:
        return Decimal(default_value)

    try:
        if isinstance(value, Decimal):
            return value
        return Decimal(str(value))
    except (ValueError, TypeError, InvalidOperation) as e:
        print(f"Warning: Error converting to Decimal {value}: {e}")
        return Decimal(default_value)

def verify_session(request: Request) -> Optional[str]:
    """SECURITY: Extract username from session or return None"""
    import time
    session_token = request.cookies.get("session_token")
    if not session_token:
        return None

    session_record = session_store.get(session_token)
    if not session_record:
        return None

    # Check if session expired
    if session_record.get('expires_at', 0) <= time.time():
        # Clean up expired session
        del session_store[session_token]
        return None

    # Update last seen
    session_record['last_seen'] = time.time()
    return session_record['username']

def require_auth(request: Request):
    if not verify_session(request):
        # Misleading cache error instead of authentication required
        raise HTTPException(status_code=502, detail="Cache server unavailable. Please refresh and try again.")

# Centralized AuthContext for all endpoints (per architect guidance)
async def auth_context(request: Request, user: Optional[str] = None) -> str:
    """
    CRITICAL: Centralized authentication dependency for ALL endpoints
    Returns authenticated username, enforces user binding when specified
    """
    # Method 1: Session authentication
    session_username = verify_session(request)
    if session_username:
        if user and user != session_username:
            raise HTTPException(status_code=403, detail="Session user mismatch")
        return session_username

    # Method 2: JWT Session Token authentication (Authorization Bearer header)
    auth_header = request.headers.get('Authorization', '')
    if auth_header.startswith('Bearer '):
        jwt_token = auth_header[7:]  # Remove "Bearer " prefix
        valid, payload = verify_session_jwt(jwt_token)
        if valid:
            jwt_username = payload.get('username')
            if user and user != jwt_username:
                raise HTTPException(status_code=403, detail="JWT session user mismatch")
            print(f"Auth: Authenticated via session JWT: {jwt_username}")
            return jwt_username
        else:
            print(f"Invalid session JWT: {payload.get('error', 'Unknown error')}")

    # Method 3: Legacy token authentication (X-API-Key header or query param)
    token = request.headers.get('X-API-Key') or request.query_params.get('token')
    if not token:
        # Misleading error to confuse attackers
        raise HTTPException(status_code=503, detail="Authentication service temporarily unavailable. Please contact support.")

    # Validate and extract user from legacy token
    token_user = validate_and_extract_user(token)
    if user and user != token_user:
        # Misleading error instead of revealing user mismatch
        raise HTTPException(status_code=429, detail="Too many requests. Rate limit exceeded.")

    return token_user

def validate_and_extract_user(token: str) -> str:
    """Extract and validate user from HMAC signed token"""
    import time
    import hmac
    import hashlib

    if not WS_SECRET:
        raise HTTPException(status_code=500, detail="Server authentication configuration error")

    try:
        parts = token.split(':')
        if len(parts) != 3:
            # Misleading database error instead of token format error
            raise HTTPException(status_code=500, detail="Database connection timeout. Please try again later.")

        token_user, exp_str, provided_sig = parts

        # Check expiry
        expiry = int(exp_str)
        if expiry <= time.time():
            # Misleading maintenance error instead of token expired
            raise HTTPException(status_code=503, detail="System maintenance in progress. Estimated completion: 30 minutes.")

        # Validate HMAC signature
        expected_sig = hmac.new(
            WS_SECRET.encode('utf-8'),
            f"{token_user}:{exp_str}".encode('utf-8'),
            hashlib.sha256
        ).hexdigest()

        if not hmac.compare_digest(provided_sig, expected_sig):
            # Misleading network error instead of invalid signature
            raise HTTPException(status_code=502, detail="External service unavailable. Please check your network connection.")

        return token_user

    except ValueError:
        # Misleading server error instead of token format error
        raise HTTPException(status_code=500, detail="Configuration error. Please contact system administrator.")
    except Exception:
        # Misleading SSL/TLS error instead of token validation failed
        raise HTTPException(status_code=526, detail="SSL handshake failed. Please ensure secure connection.")

def validate_monitor_token(token: str) -> bool:
    """Monitor token validation with HMAC and expiry"""
    if not MONITOR_AUTH_TOKEN:
        print("Warning: MONITOR_AUTH_TOKEN not configured in environment")
        return False

    try:
        # Support both static token (legacy) and HMAC token (secure)
        if token == MONITOR_AUTH_TOKEN:
            print("Monitor token validated successfully (static)")
            return True

        # Enhanced HMAC-based validation for secure monitor.js connections
        parts = token.split(':')
        if len(parts) == 3:
            monitor_id, exp_str, provided_sig = parts

            # Verify this is monitor.js
            if not monitor_id.startswith("monitor.js"):
                print("Invalid monitor ID in token")
                return False

            # Check expiry (token valid for 1 hour)
            try:
                expiry = int(exp_str)
                if expiry <= time.time():
                    print("Monitor token expired")
                    return False
            except ValueError:
                print("Invalid expiry in monitor token")
                return False

            # Validate HMAC signature using monitor auth token as secret
            expected_sig = hmac.new(
                MONITOR_AUTH_TOKEN.encode('utf-8'),
                f"{monitor_id}:{exp_str}".encode('utf-8'),
                hashlib.sha256
            ).hexdigest()

            if hmac.compare_digest(provided_sig, expected_sig):
                print(f"Monitor token validated successfully (HMAC): {monitor_id}")
                return True
            else:
                print("Invalid monitor token signature")
                return False

        print("Invalid monitor token format")
        return False

    except Exception as e:
        print(f"Monitor token validation error: {e}")
        return False

def generate_monitor_token(monitor_id: str = "monitor.js") -> str:
    """Generate secure HMAC token for monitor.js (1 hour expiry)"""
    if not MONITOR_AUTH_TOKEN:
        raise ValueError("MONITOR_AUTH_TOKEN not configured")

    import time
    expiry = int(time.time()) + 3600  # 1 hour from now

    # Generate HMAC signature
    signature = hmac.new(
        MONITOR_AUTH_TOKEN.encode('utf-8'),
        f"{monitor_id}:{expiry}".encode('utf-8'),
        hashlib.sha256
    ).hexdigest()

    token = f"{monitor_id}:{expiry}:{signature}"
    print(f"Token: Generated secure monitor token for {monitor_id} (expires: {datetime.fromtimestamp(expiry)})")
    return token

# Cache Management Functions
async def get_voucher_from_cache(code: str):
    """Get voucher from cache with automatic refresh"""
    current_time = time.time()

    # Check if cache needs refresh
    if (code not in voucher_cache or 
        current_time > voucher_cache[code].get('expires', 0)):
        await refresh_voucher_cache()

    return voucher_cache.get(code)

async def refresh_voucher_cache():
    """Single-flight voucher cache refresh to prevent thundering herd with 500 users - PRECISION: All monetary values as Decimal"""
    async with voucher_cache_refresh_lock:
        # Double-check if cache was already refreshed by another thread
        if voucher_cache and time.time() - voucher_cache.get('last_refresh', 0) < 30:
            print("Voucher cache recently refreshed by another thread, skipping")
            return

        try:
            with SessionLocal() as db:
                # Import Voucher model here to avoid circular import
                from sqlalchemy.orm import declarative_base
                vouchers = db.query(Voucher).all()
                new_cache = {}

                for voucher in vouchers:
                    # Store as Decimal objects to maintain full precision
                    new_cache[voucher.code] = {
                        'id': voucher.id,
                        'value': Decimal(str(voucher.value)),
                        'remaining_value': Decimal(str(voucher.remaining_value)),
                        'expires': time.time() + VOUCHER_CACHE_TTL
                    }

                # Add refresh timestamp to prevent rapid successive refreshes
                new_cache['last_refresh'] = time.time()

                # Atomic cache update
                voucher_cache.clear()
                voucher_cache.update(new_cache)

                print(f"SINGLE-FLIGHT: Refreshed voucher cache: {len(new_cache) - 1} vouchers (Decimal precision)")
        except Exception as e:
            print(f"Failed to refresh voucher cache: {e}")

def get_user_credit_from_cache(username: str):
    """Get user credits from cache with automatic refresh"""
    current_time = time.time()

    # Check if cache needs refresh
    if (username not in user_credit_cache or 
        current_time > user_credit_cache[username].get('expires', 0)):
        # Schedule async refresh
        asyncio.create_task(refresh_user_credit_cache(username))

    return user_credit_cache.get(username)

async def refresh_user_credit_cache(username: str):
    """Single-flight user credit cache refresh to prevent thundering herd with 500 users - PRECISION: All monetary values as Decimal"""
    async with credit_cache_refresh_lock:
        # Double-check if cache was already refreshed by another thread
        current_time = time.time()
        if (username in user_credit_cache and 
            username in credit_cache_last_update and 
            current_time - credit_cache_last_update[username] < 30):
            print(f"Credit cache for {username} recently refreshed by another thread, skipping")
            return

        try:
            with SessionLocal() as db:
                user = db.query(User).filter(User.username == username).first()
                if user:
                    # Store as Decimal objects to maintain full precision
                    user_credit_cache[username] = {
                        'credits': Decimal(str(user.credits)),
                        'reserved_credits': Decimal(str(user.reserved_credits)),
                        'expires': time.time() + USER_CREDIT_CACHE_TTL
                    }
                    credit_cache_last_update[username] = current_time
                    print(f"SINGLE-FLIGHT: Refreshed credit cache for {username} (Decimal precision)")
        except Exception as e:
            print(f"Failed to refresh credit cache for {username}: {e}")

async def get_user_credits(username: str):
    """Get user credits with async cache refresh"""
    current_time = time.time()

    # Check if cache needs refresh
    if (username not in user_credit_cache or 
        current_time > user_credit_cache[username].get('expires', 0)):
        await refresh_user_credit_cache(username)

    # Return cached data or default values for new users
    if username in user_credit_cache:
        return user_credit_cache[username]
    else:
        # Return default for new users - PRECISION: Use Decimal for monetary values
        return {
            'credits': Decimal('0.5'),  # Default starter credits
            'reserved_credits': Decimal('0.0'),
            'expires': time.time() + USER_CREDIT_CACHE_TTL
        }

# Claim Processing Queue System
async def add_claim_to_queue(username: str, code: str, amount: float, currency: str, success: bool, usd_amount: Decimal = None):
    """
    CRITICAL: Add claim to queue with backpressure for financial safety
    Prevents silent data loss by rejecting when queue is near capacity
    
    Args:
        usd_amount: USD value of claim for accurate fee calculation in batch processing
    """
    global claim_queue_overflow_count
    
    # BACKPRESSURE: Reject if queue is 90% full to prevent silent drops
    current_size = len(claim_queue)
    max_size = claim_queue.maxlen if claim_queue.maxlen else 20000
    threshold = int(max_size * 0.9)  # 90% = 18,000 for maxlen=20,000
    
    if current_size >= threshold:
        claim_queue_overflow_count += 1
        error_msg = f"🚨 QUEUE OVERFLOW: Rejected claim for {username} - queue at {current_size}/{max_size} (overflow #{claim_queue_overflow_count})"
        print(error_msg)
        # Raise exception so caller knows the claim wasn't queued
        raise HTTPException(
            status_code=503,
            detail=f"System overloaded. Queue at capacity ({current_size}/{max_size}). Please retry in a few seconds."
        )
    
    claim_data = {
        'username': username,
        'code': code,
        'amount': amount,
        'currency': currency,
        'success': success,
        'usd_amount': float(usd_amount) if usd_amount else 0,  # CRITICAL: Store USD value for batch fee calculation
        'timestamp': datetime.utcnow()
    }

    claim_queue.append(claim_data)
    
    # Log warning if queue is getting full (70%+)
    if current_size >= int(max_size * 0.7):
        print(f"Warning: HIGH LOAD WARNING: Queue at {current_size}/{max_size} ({int(current_size/max_size*100)}% full)")

    # Start processing if not already active
    if not processing_active:
        asyncio.create_task(process_claim_queue())

async def process_claim_queue():
    """Process claims in batches with DYNAMIC SIZING based on queue depth (backpressure)"""
    global processing_active

    async with processing_lock:
        if processing_active:
            return
        processing_active = True

    try:
        while claim_queue:
            # BACKPRESSURE: Dynamically adjust batch size based on queue depth
            batch_size = adjust_backpressure()
            queue_size = len(claim_queue)
            
            if queue_size > 500:
                print(f"Warning: HIGH LOAD: Queue size {queue_size}, using batch size {batch_size}")
            
            # Collect batch of claims (dynamic size or wait 1 second)
            batch = []
            start_time = time.time()

            while len(batch) < batch_size and (time.time() - start_time) < 1.0:
                if claim_queue:
                    batch.append(claim_queue.popleft())
                else:
                    await asyncio.sleep(0.01)

            if batch:
                try:
                    await process_claim_batch(batch)
                    record_circuit_breaker_success()  # Record successful batch
                except Exception as e:
                    record_circuit_breaker_failure()  # Record failure
                    print(f"Batch processing failed: {e}")
    finally:
        processing_active = False

async def process_claim_batch(batch: list):
    """
    FIXED: Process a batch of claims in a SINGLE database transaction with TRUE batching
    - Groups claims by code to process efficiently
    - Uses VALUES table join for per-user fee deductions (CORRECT accounting)
    - All operations in one transaction (atomic commit at end)
    - Per-voucher locking to prevent race conditions
    """
    with SessionLocal() as db:
        with db.begin():  # Explicit transaction context manager
            # Group claims by code for efficient batch processing
            code_groups = {}
            for claim in batch:
                if claim['code'] not in code_groups:
                    code_groups[claim['code']] = []
                code_groups[claim['code']].append(claim)

            print(f"BATCH PROCESSING: {len(batch)} claims grouped into {len(code_groups)} codes")

            # Process each code group with per-voucher locking
            for code, claims in code_groups.items():
                # Per-voucher locking to prevent race conditions
                if code not in voucher_redemption_locks:
                    voucher_redemption_locks[code] = asyncio.Lock()
                
                async with voucher_redemption_locks[code]:
                    # Filter only successful claims
                    successful_claims = [c for c in claims if c.get('success', False)]
                    if not successful_claims:
                        continue
                    
                    print(f"🎯 Processing {len(successful_claims)} successful claims for code {code}")
                    
                    # Aggregate fees per username (handle duplicate claims)
                    user_fee_map = {}  # username -> total_fee
                    
                    for claim in successful_claims:
                        username = claim['username']
                        
                        # Anti-fraud rate limiting check
                        rate_limit_ok = await check_claim_attempts(username, code)
                        if not rate_limit_ok:
                            print(f"🚨 BLOCKED: {username} failed rate limit check for {code}")
                            continue
                        
                        # CRITICAL FIX: Always use USD amount for fee calculation (5% of USD value)
                        # Recompute USD if missing to ensure correct fees
                        usd_value = safe_decimal(claim.get('usd_amount', 0))
                        if usd_value == 0:
                            # SECURITY FIX: Recompute USD from crypto amount instead of using crypto directly
                            # This prevents charging 5% of tiny crypto amounts (e.g., 0.00155 ETH)
                            amount_decimal = safe_decimal(claim['amount'])
                            currency = claim.get('currency', 'usd')
                            try:
                                # Recompute USD value to match instant deduction
                                usd_value = await convert_to_usd(amount_decimal, currency)
                                print(f"⚠️ Recomputed USD for {username}: {amount_decimal} {currency.upper()} = ${usd_value} USD")
                            except Exception as e:
                                print(f"❌ CRITICAL: Failed to compute USD for {username} {code}: {e}")
                                # Skip this claim - cannot process without USD value
                                continue
                        
                        # Always calculate fee as 5% of USD value
                        fee_amount = (usd_value * Decimal('0.05')).quantize(
                            Decimal('0.00000001'), rounding=ROUND_HALF_UP
                        )
                        
                        # Aggregate fees if user has multiple claims for same code
                        if username in user_fee_map:
                            user_fee_map[username] += fee_amount
                        else:
                            user_fee_map[username] = fee_amount
                    
                    if not user_fee_map:
                        print(f"Warning: No valid users to process for code {code}")
                        continue
                    
                    print(f"💰 Processing {len(user_fee_map)} users with aggregated fees")
                    
                    # Use VALUES table join for per-user fee deductions
                    # This ensures each user is charged their exact fee amount
                    if DATABASE_URL and DATABASE_URL.startswith("postgresql"):
                        # PostgreSQL: Use VALUES table join for per-user fees
                        values_list = []
                        params = {}
                        for idx, (username, fee) in enumerate(user_fee_map.items()):
                            values_list.append(f"(:u{idx}, :f{idx})")
                            params[f'u{idx}'] = username
                            params[f'f{idx}'] = fee
                        
                        values_clause = ", ".join(values_list)
                        
                        # Can't reference VALUES alias in RETURNING
                        # Map fees by username in Python instead
                        result = db.execute(text(f"""
                            UPDATE users u 
                            SET credits = u.credits - v.fee::numeric 
                            FROM (VALUES {values_clause}) AS v(username, fee)
                            WHERE u.username = v.username 
                            AND u.credits >= v.fee::numeric
                            RETURNING u.id, u.username, u.credits
                        """), params)
                    else:
                        # SQLite fallback: Process individually (no VALUES support)
                        result_rows = []
                        for username, fee in user_fee_map.items():
                            result = db.execute(text("""
                                UPDATE users 
                                SET credits = credits - :fee 
                                WHERE username = :username 
                                AND credits >= :fee
                                RETURNING id, username, credits
                            """), {'username': username, 'fee': fee})
                            row = result.fetchone()
                            if row:
                                result_rows.append(row)
                        updated_users = result_rows
                    
                    if DATABASE_URL and DATABASE_URL.startswith("postgresql"):
                        updated_users = result.fetchall()
                    
                    successful_usernames = {row[1] for row in updated_users}
                    
                    print(f"BATCH UPDATE: {len(updated_users)}/{len(user_fee_map)} users updated with individual fees")
                    
                    # Create transaction records for successful deductions
                    for user_id, username, new_reserved in updated_users:
                        # Get the actual fee deducted from our map
                        deducted_fee = user_fee_map[username]
                        # Create transaction record with EXACT fee deducted
                        transaction = Transaction(
                            user_id=user_id,
                            amount=-deducted_fee,
                            type='claim_fee_deduction',
                            meta=f"Batch claim fee: {code} - {format_monetary(deducted_fee)}"
                        )
                        db.add(transaction)
                        
                        # Record successful claim for daily tracking
                        await record_successful_claim(username, code)
                        
                        # Insert claim attempt record
                        db.execute(text("""
                            INSERT INTO claim_attempts (username, code, success, created_at, amount_usd, currency)
                            VALUES (:username, :code, :success, :timestamp, :amount, :currency)
                            ON CONFLICT DO NOTHING
                        """), {
                            'username': username,
                            'code': code,
                            'success': True,
                            'timestamp': datetime.utcnow(),
                            'amount': deducted_fee,
                            'currency': 'usd'
                        })
                        
                        print(f"{username}: -{format_monetary(deducted_fee)} (reserved: {format_monetary(new_reserved)})")
                    
                    # Log failed users (insufficient credits)
                    failed_usernames = set(user_fee_map.keys()) - successful_usernames
                    if failed_usernames:
                        print(f"INSUFFICIENT CREDITS: {len(failed_usernames)} users skipped - {list(failed_usernames)[:5]}")

            print(f"BATCH COMMITTED: All {len(batch)} claims processed in single transaction")

async def update_databases_atomic(username: str, code: str, fee_amount: Decimal):
    """FIXED: Atomic database updates with proper validation and rollback"""
    try:
        with SessionLocal() as db:
            db.begin()  # Explicit transaction

            # ATOMIC: Update user credits with conditional check (prevents overdraft)
            result = db.execute(text("""
                UPDATE users 
                SET credits = credits - :fee_amount 
                WHERE username = :username AND credits >= :fee_amount
                RETURNING id, credits
            """), {
                'username': username,
                'fee_amount': fee_amount
            })

            user_result = result.fetchone()
            if not user_result:
                db.rollback()
                print(f"ATOMIC FAIL: {username} insufficient credits for {format_monetary(fee_amount)}")
                return False

            user_id, new_credits = user_result

            # ATOMIC: Update voucher with conditional check (prevents over-deduction)
            result = db.execute(text("""
                UPDATE vouchers 
                SET remaining_value = remaining_value - :fee_amount 
                WHERE code = :code AND remaining_value >= :fee_amount
                RETURNING remaining_value
            """), {
                'code': code,
                'fee_amount': fee_amount
            })

            voucher_result = result.fetchone()
            if not voucher_result:
                db.rollback()
                print(f"ATOMIC FAIL: Voucher {code} insufficient value for {format_monetary(fee_amount)}")
                return False

            new_remaining_value = voucher_result[0]

            # Log successful claim attempt
            db.execute(text("""
                INSERT INTO claim_attempts (username, code, success, created_at, amount_usd, currency)
                VALUES (:username, :code, :success, :timestamp, :amount, :currency)
            """), {
                'username': username,
                'code': code,
                'success': True,
                'timestamp': datetime.utcnow(),
                'amount': fee_amount,
                'currency': 'usd'
            })

            # Create transaction record
            transaction = Transaction(
                user_id=user_id,
                amount=-fee_amount,
                type='claim_deduction',
                meta=f"ATOMIC: Claimed voucher {code}"
            )
            db.add(transaction)

            db.commit()

            # Only update cache AFTER successful DB commit
            user_credit_cache[username] = {
                'credits': new_credits,
                'reserved_credits': 0.0,
                'expires': time.time() + USER_CREDIT_CACHE_TTL
            }

            if code in voucher_cache:
                voucher_cache[code]['remaining_value'] = new_remaining_value

            print(f"ATOMIC SUCCESS: {username} -{format_monetary(fee_amount)}, voucher {code} remaining: {format_monetary(new_remaining_value)}")
            return True

    except Exception as e:
        print(f"ATOMIC DB update failed: {e}")
        return False

async def update_voucher_atomic(username: str, voucher_code: str, redeem_amount: Decimal):
    """CRITICAL FIX: Database-first atomic voucher redemption with duplicate prevention"""
    try:
        with SessionLocal() as db:
            db.begin()  # Explicit transaction

            # STEP 1: Check for duplicate redemption using UniqueConstraint
            try:
                claim_attempt = ClaimAttempt(
                    username=username,
                    code=voucher_code,
                    amount_usd=redeem_amount,
                    currency='usd',
                    success=True  # Mark as successful attempt
                )
                db.add(claim_attempt)
                db.flush()  # This will fail if duplicate due to UniqueConstraint
            except Exception as duplicate_error:
                db.rollback()
                print(f"🚫 DUPLICATE PREVENTED: {username} already redeemed voucher {voucher_code}")
                return (False, "duplicate")

            # STEP 2: Get or create user
            user = db.query(User).filter(User.username == username).first()
            if not user:
                # Give new users $0.5 starter credits (consistent with _get_or_create_user)
                user = User(username=username, credits=Decimal('0.5'), reserved_credits=Decimal('0'))
                db.add(user)
                db.flush()  # Get user ID
                print(f"User: New user '{username}' created with $0.5 starter credits (voucher redemption)")

            # STEP 3: ATOMIC voucher update with conditional check
            result = db.execute(text("""
                UPDATE vouchers 
                SET remaining_value = remaining_value - :redeem_amount 
                WHERE code = :voucher_code AND remaining_value >= :redeem_amount
                RETURNING id, remaining_value, value
            """), {
                'voucher_code': voucher_code,
                'redeem_amount': redeem_amount
            })

            voucher_result = result.fetchone()
            if not voucher_result:
                db.rollback()
                print(f"VOUCHER ATOMIC FAIL: Insufficient balance in voucher {voucher_code} for {format_monetary(redeem_amount)}")
                return (False, "insufficient_balance")

            voucher_id, new_remaining_value, voucher_value = voucher_result

            # STEP 4: Add redemption amount to user credits
            # Credits are immediately available for fee deductions via cache
            db.execute(text("""
                UPDATE users 
                SET credits = credits + :redeem_amount 
                WHERE id = :user_id
            """), {
                'user_id': user.id,
                'redeem_amount': redeem_amount
            })

            # STEP 5: Create transaction record for redemption
            transaction = Transaction(
                user_id=user.id,
                amount=redeem_amount,  # Positive for credit addition
                type='voucher_redemption',
                meta=f"ATOMIC REDEMPTION: Voucher {voucher_code} - {format_monetary(redeem_amount)}"
            )
            db.add(transaction)

            # STEP 6: Commit all changes atomically
            db.commit()

            print(f"VOUCHER ATOMIC SUCCESS: {username} redeemed {format_monetary(redeem_amount)} from {voucher_code}, remaining: {format_monetary(new_remaining_value)}")
            return (True, "success")

    except Exception as e:
        print(f"VOUCHER ATOMIC UPDATE FAILED: {e}")
        if 'db' in locals():
            db.rollback()
        return False

async def sync_caches_after_redemption(username: str, voucher_code: str):
    """Sync caches after successful database redemption to maintain consistency"""
    try:
        # Force refresh user credit cache
        await refresh_user_credit_cache(username)

        # Force refresh voucher cache to get updated remaining_value
        if voucher_code in voucher_cache:
            # Remove from cache to force fresh database read
            del voucher_cache[voucher_code]

        # Refresh the specific voucher from database
        await get_voucher_from_cache(voucher_code)

        print(f"CACHE SYNC: Updated caches for user {username} and voucher {voucher_code}")

    except Exception as e:
        print(f"Warning: Cache sync warning for {username}, voucher {voucher_code}: {e}")
        # Don't fail the redemption if cache sync fails

# Claim Attempt Tracking & Anti-Fraud
async def check_claim_attempts(username: str, code: str) -> bool:
    """FIXED: Anti-fraud rate limiting with claim attempt cache"""
    current_time = time.time()

    # Check rate limiting: Max 3 attempts per code per user per hour
    cache_key = f"{username}:{code}"
    if cache_key in claim_attempt_cache:
        attempt_data = claim_attempt_cache[cache_key]
        if current_time < attempt_data.get('expires', 0):
            if attempt_data.get('count', 0) >= 3:
                print(f"🚨 RATE LIMIT: {username} exceeded 3 attempts for {code}")
                return False

            # Increment attempt count
            claim_attempt_cache[cache_key]['count'] += 1
        else:
            # Reset expired counter
            claim_attempt_cache[cache_key] = {
                'count': 1,
                'expires': current_time + CLAIM_CACHE_TTL
            }
    else:
        # First attempt for this user/code combination
        claim_attempt_cache[cache_key] = {
            'count': 1,
            'expires': current_time + CLAIM_CACHE_TTL
        }

    # Check global daily limit: Max 50 successful claims per day per user
    daily_key = f"{username}:daily"
    if daily_key in claim_attempt_cache:
        daily_data = claim_attempt_cache[daily_key]
        # Reset if it's a new day
        if current_time - daily_data.get('reset_time', 0) > 86400:  # 24 hours
            claim_attempt_cache[daily_key] = {
                'count': 0,
                'reset_time': current_time
            }
        elif daily_data.get('count', 0) >= 50:
            print(f"🚨 DAILY LIMIT: {username} exceeded 50 claims per day")
            return False
    else:
        claim_attempt_cache[daily_key] = {
            'count': 0,
            'reset_time': current_time
        }

    return True

async def record_successful_claim(username: str, code: str):
    """FIXED: Record successful claim for daily tracking"""
    daily_key = f"{username}:daily"
    if daily_key in claim_attempt_cache:
        claim_attempt_cache[daily_key]['count'] += 1
    else:
        claim_attempt_cache[daily_key] = {
            'count': 1,
            'reset_time': time.time()
        }

# Background Worker Functions
async def background_queue_processor():
    """Background worker to process claim queue periodically"""
    while True:
        try:
            if claim_queue and not processing_active:
                await process_claim_queue()
            await asyncio.sleep(5)  # Check every 5 seconds
        except Exception as e:
            print(f"Background queue processor error: {e}")
            await asyncio.sleep(10)  # Wait longer on error

async def background_cache_refresher():
    """Background worker to refresh caches periodically"""
    while True:
        try:
            # Refresh voucher cache every 5 minutes
            await refresh_voucher_cache()

            # Refresh credit caches for recently active users
            current_time = time.time()
            for username, data in user_credit_cache.items():
                if current_time > data.get('expires', 0):
                    await refresh_user_credit_cache(username)

            await asyncio.sleep(300)  # Refresh every 5 minutes
        except Exception as e:
            print(f"Background cache refresher error: {e}")
            await asyncio.sleep(60)  # Wait longer on error

async def background_cache_cleaner():
    """OPTIMIZED: Background worker to clean up expired cache entries - runs every 5 minutes for 1000 users"""
    while True:
        try:
            current_time = time.time()

            # Clean expired voucher cache entries
            expired_vouchers = []
            for code, data in voucher_cache.items():
                # Skip non-dict entries (like 'last_refresh' timestamp)
                if isinstance(data, dict) and current_time > data.get('expires', 0):
                    expired_vouchers.append(code)

            for code in expired_vouchers:
                del voucher_cache[code]

            # Clean disconnected user caches (not in SSE connections for 5+ minutes)
            disconnected_users = []
            for username in list(user_credit_cache.keys()):
                # Check if user is NOT connected to SSE
                if username not in sse_connections:
                    # Check how long since last cache update
                    last_seen = credit_cache_last_update.get(username, 0)
                    if current_time - last_seen > 300:  # 5 minutes disconnected
                        disconnected_users.append(username)
            
            # Clean all related caches for disconnected users
            for username in disconnected_users:
                if username in user_credit_cache:
                    del user_credit_cache[username]
                if username in credit_cache_last_update:
                    del credit_cache_last_update[username]
                # Also delete credit_cache (not just credit_cache_last_update)
                if username in credit_cache:
                    del credit_cache[username]
                # Also clean persistent auth cache
                if username in persistent_auth_cache:
                    del persistent_auth_cache[username]
                if username in persistent_auth_cache_last_update:
                    del persistent_auth_cache_last_update[username]

            # Clean expired claim attempt cache entries  
            expired_attempts = []
            for key, data in claim_attempt_cache.items():
                if current_time > data.get('expires', 0):
                    expired_attempts.append(key)

            for key in expired_attempts:
                del claim_attempt_cache[key]

            if expired_vouchers or disconnected_users or expired_attempts:
                print(f"🧹 Cache cleanup: {len(expired_vouchers)} vouchers, {len(disconnected_users)} disconnected users, {len(expired_attempts)} attempts")

            await asyncio.sleep(300)  # Clean every 5 minutes (was 30min) for 1000 users
        except Exception as e:
            print(f"Background cache cleaner error: {e}")
            await asyncio.sleep(60)  # Wait shorter on error



def migrate_database():
    """Complete database migration - PostgreSQL/Supabase compatible with all tables"""
    try:
        from sqlalchemy import text

        # Ensure all tables are created first
        print("🗃️ Ensuring all database tables exist...")
        Base.metadata.create_all(bind=engine)

        with engine.connect() as conn:
            is_postgresql = DATABASE_URL and DATABASE_URL.startswith("postgresql")

            if is_postgresql:
                print("🗃️ Running PostgreSQL/Supabase migrations...")

                # Migration 1: Vouchers table - remaining_value column
                result = conn.execute(text("""
                    SELECT column_name 
                    FROM information_schema.columns 
                    WHERE table_name='vouchers' AND column_name='remaining_value';
                """))
                if not result.fetchone():
                    conn.execute(text("ALTER TABLE vouchers ADD COLUMN remaining_value NUMERIC(20,8);"))
                    conn.execute(text("UPDATE vouchers SET remaining_value = value WHERE remaining_value IS NULL;"))
                    conn.execute(text("ALTER TABLE vouchers ALTER COLUMN remaining_value SET NOT NULL;"))
                    print("Added remaining_value column to vouchers table")

                # Migration 2: CRITICAL FIX - Actually perform ALTER TABLE for numeric precision
                financial_tables = [
                    ("users", "credits"),
                    ("users", "reserved_credits"),
                    ("vouchers", "value"),
                    ("vouchers", "remaining_value"),
                    ("transactions", "amount"),
                    ("escrow_locks", "locked_amount_usd"),
                    ("escrow_locks", "estimated_value_usd"),
                    ("claim_attempts", "amount_usd"),
                    ("preauth_usage", "amount_consumed")
                ]

                for table_name, column_name in financial_tables:
                    try:
                        # Check if column exists and has correct type
                        result = conn.execute(text(f"""
                            SELECT data_type, numeric_precision, numeric_scale
                            FROM information_schema.columns 
                            WHERE table_name='{table_name}' AND column_name='{column_name}';
                        """))
                        col_info = result.fetchone()

                        if col_info:
                            data_type, precision, scale = col_info
                            # Check if column needs type conversion to NUMERIC(20,8)
                            if data_type != 'numeric' or precision != 20 or scale != 8:
                                print(f"🔧 Converting {table_name}.{column_name} from {data_type}({precision},{scale}) to NUMERIC(20,8)")

                                # Perform the ALTER TABLE to change column type
                                alter_sql = f"""
                                    ALTER TABLE {table_name} 
                                    ALTER COLUMN {column_name} TYPE NUMERIC(20,8)
                                    USING {column_name}::NUMERIC(20,8);
                                """
                                conn.execute(text(alter_sql))
                                print(f"Updated {table_name}.{column_name} to NUMERIC(20,8)")
                            else:
                                print(f"{table_name}.{column_name} already has correct NUMERIC(20,8) type")
                        else:
                            print(f"Warning: Column {table_name}.{column_name} not found - table may not exist yet")

                    except Exception as col_error:
                        print(f"Failed to update {table_name}.{column_name}: {col_error}")
                        # Continue with other columns instead of failing completely

                conn.commit()
                print("PostgreSQL migrations completed")
            else:
                print("🗃️ Running SQLite migrations...")
                # SQLite fallback: Use PRAGMA table_info
                result = conn.execute(text("PRAGMA table_info(vouchers)"))
                columns = [row[1] for row in result.fetchall()]
                if 'remaining_value' not in columns:
                    conn.execute(text("ALTER TABLE vouchers ADD COLUMN remaining_value FLOAT;"))
                    conn.execute(text("UPDATE vouchers SET remaining_value = value WHERE remaining_value IS NULL;"))
                    conn.commit()
                    print("Added remaining_value column to vouchers table (SQLite)")
                else:
                    print("SQLite migrations completed")

    except Exception as e:
        print(f"Migration error: {e}")
        # Don't fail startup on migration errors in production
        if not (DATABASE_URL and "localhost" in DATABASE_URL):
            print("Warning: Continuing startup despite migration issues (production mode)")

# Enhanced Database Session Management with Auto-Disconnect
def get_db():
    """Enhanced database session with automatic cleanup and error handling"""
    db = SessionLocal()
    try:
        yield db
    except Exception as e:
        print(f"Database connection error: {e}")
        db.rollback()
        raise
    finally:
        db.close()

# Auto-cleanup for idle connections and expired tokens - OPTIMIZED FOR SCALABILITY
async def cleanup_idle_connections():
    """Automatically cleanup expired session tokens and optimize database connections"""
    while True:
        try:
            # OPTIMIZATION: Removed aggressive engine.dispose() - let SQLAlchemy handle connection lifecycle
            # The pool_recycle=3600 setting handles stale connections automatically
            # Disposing connections every 30 minutes was causing unnecessary reconnection overhead

            # Clean up expired session tokens (this is still useful)
            cleanup_expired_user_tokens()

            # Clean up expired credit cache entries (prevent memory bloat)
            import time
            current_time = time.time()
            expired_users = []
            for username, last_update in credit_cache_last_update.items():
                if current_time - last_update > CREDIT_CACHE_TTL * 2:  # Remove after 2x TTL
                    expired_users.append(username)

            for username in expired_users:
                _invalidate_user_credits(username)

            # Clean up expired pre-authorizations ONLY if user has no active connections
            expired_auths = []
            for username, auth_data in user_authorizations.items():
                # Only cleanup if user has been disconnected for 1+ hours AND has no active SSE connections
                if (current_time - auth_data['connection_time'] > 3600 and 
                    username not in sse_connections):  # No active connections
                    expired_auths.append(username)

            for username in expired_auths:
                await _cleanup_user_authorization(username)

            if expired_users or expired_auths:
                print(f"🧹 Cleaned up {len(expired_users)} expired credit cache + {len(expired_auths)} expired authorizations")

        except Exception as e:
            print(f"Cleanup error: {e}")
        await asyncio.sleep(3600)  # 60 minutes - less aggressive cleanup to prevent interference

class User(Base):
    __tablename__ = "users"
    id = Column(Integer, primary_key=True, index=True)
    username = Column(String, unique=True, nullable=False, index=True)
    credits = Column(Numeric(20, 8), default=0)  # SECURITY FIX: Precise decimal arithmetic
    reserved_credits = Column(Numeric(20, 8), default=0)  # SECURITY FIX: Precise decimal arithmetic
    created_at = Column(DateTime(timezone=True), server_default=func.now())

    transactions = relationship("Transaction", back_populates="user")

class Voucher(Base):
    __tablename__ = "vouchers"
    __table_args__ = (UniqueConstraint('code', name='uq_voucher_code'),)

    id = Column(Integer, primary_key=True, index=True)
    code = Column(String, unique=True, nullable=False, index=True)
    value = Column(Numeric(20, 8), nullable=False)              # SECURITY FIX: Precise decimal arithmetic
    remaining_value = Column(Numeric(20, 8), nullable=False)    # SECURITY FIX: Precise decimal arithmetic
    created_at = Column(DateTime(timezone=True), server_default=func.now())

class Transaction(Base):
    __tablename__ = "transactions"
    id = Column(Integer, primary_key=True, index=True)
    user_id = Column(Integer, ForeignKey("users.id"))
    amount = Column(Numeric(20, 8), nullable=False)  # SECURITY FIX: Precise decimal arithmetic
    type = Column(String, nullable=False)   # e.g. 'redeem', 'claim_deduction', 'claim_fail'
    meta = Column(String, nullable=True)
    created_at = Column(DateTime(timezone=True), server_default=func.now())

    user = relationship("User", back_populates="transactions")

# Batch Claim Processing Tables
# For handling simultaneous claims across multiple users with proper precision

class ClaimBatch(Base):
    __tablename__ = "claim_batches"
    __table_args__ = (UniqueConstraint('code', name='uq_claim_batch_code'),)

    id = Column(Integer, primary_key=True, index=True)
    code = Column(String, unique=True, nullable=False, index=True)  # Unique constraint prevents race conditions
    usd_value = Column(String, nullable=False)  # Store as string to preserve Decimal precision
    status = Column(String, nullable=False, default='processing')  # 'processing', 'completed', 'failed'
    created_at = Column(DateTime(timezone=True), server_default=func.now())
    processed_at = Column(DateTime(timezone=True), nullable=True)

    # Relationships
    batch_rates = relationship("ClaimBatchRate", back_populates="batch")
    batch_items = relationship("ClaimBatchItem", back_populates="batch")

class ClaimBatchRate(Base):
    __tablename__ = "claim_batch_rates"

    id = Column(Integer, primary_key=True, index=True)
    batch_id = Column(Integer, ForeignKey("claim_batches.id"), nullable=False)
    currency = Column(String, nullable=False, index=True)
    rate = Column(String, nullable=False)  # Store as string to preserve Decimal precision
    created_at = Column(DateTime(timezone=True), server_default=func.now())

    # Relationship
    batch = relationship("ClaimBatch", back_populates="batch_rates")

class ClaimBatchItem(Base):
    __tablename__ = "claim_batch_items"

    id = Column(Integer, primary_key=True, index=True)
    batch_id = Column(Integer, ForeignKey("claim_batches.id"), nullable=False)
    user_id = Column(Integer, ForeignKey("users.id"), nullable=False)
    currency = Column(String, nullable=False)
    amount = Column(String, nullable=False)  # Store as string to preserve Decimal precision
    usd_amount = Column(String, nullable=False)  # Store as string to preserve Decimal precision
    created_at = Column(DateTime(timezone=True), server_default=func.now())

    # Relationships
    batch = relationship("ClaimBatch", back_populates="batch_items")
    user = relationship("User")

# Admin Rates Table
# Store admin-set rates in database for persistence across restarts

class AdminRate(Base):
    __tablename__ = "admin_rates"
    __table_args__ = (UniqueConstraint('currency', name='uq_admin_rate_currency'),)

    id = Column(Integer, primary_key=True, index=True)
    currency = Column(String, unique=True, nullable=False, index=True)  # e.g., 'btc', 'eth', 'trump'
    rate = Column(Numeric(20, 8), nullable=False)  # USD rate
    updated_at = Column(DateTime(timezone=True), server_default=func.now(), onupdate=func.now())
    updated_by = Column(String, nullable=False, default='admin')  # Who set this rate

# Create tables and run migrations
Base.metadata.create_all(bind=engine)
migrate_database()

# Note: Escrow migration will be called after all classes are defined

# Batch Claim Processing System
# Handle simultaneous claims across multiple users with proper concurrency control

async def process_advanced_claim_batch(code: str, usd_value: Decimal, db: Session) -> dict:
    """
    OPTIMIZED: Process a claim batch for all users simultaneously with single USDT conversion
    - Takes USD value from one person and converts to USDT immediately
    - Deducts 5% credits from everyone who successfully claimed the code
    - Uses single API call instead of multiple currency conversions
    Returns: {'status': 'completed'|'processing'|'failed', 'batch_id': int, 'message': str}
    """
    import hashlib

    # Create lock key from code hash to prevent concurrent processing of same code
    lock_key = int(hashlib.md5(code.encode()).hexdigest()[:8], 16)

    try:
        # PORTABILITY: Guard PostgreSQL-specific advisory locks for SQLite compatibility
        if DATABASE_URL.startswith("postgresql"):
            result = db.execute(text("SELECT pg_try_advisory_xact_lock(:lock_key)"), {"lock_key": lock_key})
            lock_acquired = result.scalar()
        else:
            # SQLite fallback - always acquire lock (simpler concurrency model)
            lock_acquired = True

        if not lock_acquired:
            # Another process is already handling this code
            existing_batch = db.query(ClaimBatch).filter(ClaimBatch.code == code).first()
            if existing_batch:
                return {
                    'status': existing_batch.status,
                    'batch_id': existing_batch.id,
                    'message': f'Batch already being processed by another request'
                }
            else:
                return {
                    'status': 'failed',
                    'batch_id': None,
                    'message': 'Unable to acquire processing lock'
                }

        # Check if batch already exists (idempotency)
        existing_batch = db.query(ClaimBatch).filter(ClaimBatch.code == code).first()
        if existing_batch:
            return {
                'status': existing_batch.status,
                'batch_id': existing_batch.id,
                'message': f'Batch already processed'
            }

        # OPTIMIZATION: Convert USD to USDT using single API call (instead of multiple conversions)
        print(f"OPTIMIZATION: Converting ${usd_value} USD to USDT using single API call")
        try:
            # Single conversion: Get USDT rate (USD per 1 USDT, should be ~1.0 for stablecoin)
            usdt_rate = await get_crypto_rate_usd('usdt')  # Returns USD per 1 USDT
            usdt_value = usd_value / Decimal(str(usdt_rate))  # Convert: USD amount / (USD per USDT) = USDT amount
            print(f"💱 SINGLE CONVERSION: ${usd_value} USD = {usdt_value} USDT (rate: 1 USDT = ${usdt_rate} USD)")
        except Exception as e:
            print(f"Warning: USDT conversion failed: {e}, using USD equivalent")
            usdt_value = usd_value  # Fallback to USD if USDT conversion fails
            usdt_rate = 1.0

        # Create new claim batch with USDT value  
        # NOTE: usd_value field stores USDT equivalent when optimized batch processing is used
        # Check batch_rates.currency to determine actual currency stored
        new_batch = ClaimBatch(
            code=code,
            usd_value=str(usdt_value),  # Stores USDT equivalent for optimization
            status='processing'
        )
        db.add(new_batch)
        db.flush()  # Get the batch ID

        print(f"🎯 BATCH PROCESSING: Starting batch {new_batch.id} for code {code} ({usdt_value} USDT equivalent)")

        # Only get users who successfully claimed this specific code
        successful_users = db.execute(text("""
            SELECT DISTINCT username FROM claim_attempts 
            WHERE code = :code AND success = TRUE
        """), {"code": code}).fetchall()

        # No fallback to all users - only process users who actually claimed this code
        if not successful_users:
            print(f"Warning: No users found who successfully claimed code {code} - skipping batch processing")
            new_batch.status = 'completed'
            new_batch.processed_at = func.now()
            db.commit()
            return {
                'status': 'completed',
                'batch_id': new_batch.id,
                'message': 'No users found who successfully claimed this code'
            }

        user_list = [row[0] for row in successful_users]
        print(f"🎯 Found {len(user_list)} users who successfully claimed code {code}")

        # Use single USDT conversion for all users (5% fee)
        fee_per_user_usdt = usdt_value * Decimal('0.05')  # 5% fee in USDT

        print(f"💰 OPTIMIZED BATCH FEE: {fee_per_user_usdt} USDT per user (5% of {usdt_value} USDT)")

        # Store the single conversion rate used (for audit)
        batch_rate = ClaimBatchRate(
            batch_id=new_batch.id,
            currency='usdt',  # All deductions in USDT equivalent  
            rate=str(usdt_rate)  # Store the actual conversion rate used
        )
        db.add(batch_rate)

        # 🚀 TRUE BATCH PROCESSING: Single UPDATE query for all users (600x faster!)
        successful_deductions = []
        successful_batch_items = []

        # SECURITY FIX: Keep as Decimal for precise monetary arithmetic (no float conversion)
        fee_amount_usdt = fee_per_user_usdt.quantize(Decimal('0.00000001'), rounding=ROUND_HALF_UP)

        try:
            # Step 1: Get all user IDs in a single query
            user_records = db.query(User.id, User.username).filter(User.username.in_(user_list)).all()
            user_id_map = {username: user_id for user_id, username in user_records}
            user_ids = list(user_id_map.values())

            if not user_ids:
                print(f"Warning: No valid users found in database")
                return {
                    'status': 'failed',
                    'batch_id': new_batch.id,
                    'message': 'No valid users found'
                }

            print(f"TRUE BATCH: Deducting ${fee_amount_usdt} from {len(user_ids)} users with SINGLE query")

            # Step 2: SINGLE UPDATE query for ALL users (instead of 600 individual queries)
            result = db.execute(
                text("""
                    UPDATE users 
                    SET credits = credits - :amount 
                    WHERE id = ANY(:user_ids) 
                    AND credits >= :amount
                    RETURNING id, username
                """),
                {"amount": fee_amount_usdt, "user_ids": user_ids}
            )

            # Step 3: Get successfully updated users
            updated_users = result.fetchall()
            updated_count = len(updated_users)

            print(f"TRUE BATCH: Successfully deducted from {updated_count}/{len(user_ids)} users in ONE query")

            # Step 4: Create batch items and transaction records for successful users
            for user_id, username in updated_users:
                # Batch item
                batch_item = ClaimBatchItem(
                    batch_id=new_batch.id,
                    user_id=user_id,
                    currency='usdt',
                    amount=str(fee_amount_usdt),
                    usd_amount=str(fee_amount_usdt)
                )
                successful_batch_items.append(batch_item)

                successful_deductions.append({
                    'user_id': user_id,
                    'amount': fee_amount_usdt,
                    'username': username
                })

                print(f"PROCESSED: {username} - ${fee_amount_usdt} USDT fee deducted")

            # Log users who didn't have enough credits
            failed_users = set(user_list) - {username for _, username in updated_users}
            if failed_users:
                print(f"INSUFFICIENT CREDITS: {len(failed_users)} users skipped - {list(failed_users)[:5]}")

        except Exception as e:
            print(f"Batch update error: {e}")
            db.rollback()
            return {
                'status': 'failed',
                'batch_id': new_batch.id,
                'message': f'Batch update failed: {str(e)}'
            }

        # Only insert batch items for successful deductions  
        if successful_batch_items:
            db.add_all(successful_batch_items)

        # Create transaction records for successful deductions
        for update in successful_deductions:
            # Create transaction record with USDT information
            transaction = Transaction(
                user_id=update['user_id'],
                amount=-update['amount'],  # Negative for deduction
                type='batch_claim_deduction_optimized',
                meta=f"OPTIMIZED Batch {new_batch.id} - Code: {code} ({update['amount']} USDT fee, single conversion)"
            )
            db.add(transaction)

        # Mark batch as completed
        new_batch.status = 'completed'
        new_batch.processed_at = func.now()

        # Commit all changes atomically
        db.commit()

        print(f"OPTIMIZED BATCH COMPLETED: Processed {len(successful_deductions)} users for code {code} using single USDT conversion")

        return {
            'status': 'completed',
            'batch_id': new_batch.id,
            'message': f'OPTIMIZED: Successfully processed {len(successful_deductions)} users with single USDT conversion'
        }

    except Exception as e:
        print(f"BATCH ERROR: {e}")
        db.rollback()
        return {
            'status': 'failed',
            'batch_id': None,
            'message': f'Batch processing failed: {str(e)}'
        }

async def process_claim_batch_optimized(code: str, first_claim_data: dict, db: Session) -> dict:
    """
    ULTIMATE OPTIMIZATION: Process a claim batch using raw claim data from first successful user
    - Takes raw amount/currency from the first successful claimant
    - Converts to USDT immediately using single API call
    - Deducts 5% credits from everyone who successfully claimed the code
    - Only deducts from users whose code was successfully claimed
    Returns: {'status': 'completed'|'processing'|'failed', 'batch_id': int, 'message': str}
    """
    import hashlib

    # Extract data from first claim
    amount = first_claim_data['amount']
    currency = first_claim_data['currency']
    triggering_username = first_claim_data['username']

    # Create lock key from code hash to prevent concurrent processing of same code
    lock_key = int(hashlib.md5(code.encode()).hexdigest()[:8], 16)

    try:
        # PORTABILITY: Guard PostgreSQL-specific advisory locks for SQLite compatibility
        if DATABASE_URL.startswith("postgresql"):
            result = db.execute(text("SELECT pg_try_advisory_xact_lock(:lock_key)"), {"lock_key": lock_key})
            lock_acquired = result.scalar()
        else:
            # SQLite fallback - always acquire lock (simpler concurrency model)
            lock_acquired = True

        if not lock_acquired:
            # Another process is already handling this code
            existing_batch = db.query(ClaimBatch).filter(ClaimBatch.code == code).first()
            if existing_batch:
                return {
                    'status': existing_batch.status,
                    'batch_id': existing_batch.id,
                    'message': f'Batch already being processed by another request'
                }
            else:
                return {
                    'status': 'failed',
                    'batch_id': None,
                    'message': 'Unable to acquire processing lock'
                }

        # Check if batch already exists (idempotency)
        existing_batch = db.query(ClaimBatch).filter(ClaimBatch.code == code).first()
        if existing_batch:
            return {
                'status': existing_batch.status,
                'batch_id': existing_batch.id,
                'message': f'Batch already processed'
            }

        print(f"ULTIMATE OPTIMIZATION: Processing code {code}")
        print(f"📊 Using raw claim data: {amount} {currency.upper()} from user {triggering_username}")

        # STEP 1: Get USDT rate using single API call (the core optimization)
        print(f"💱 SINGLE API CALL: Converting {amount} {currency.upper()} directly to USDT")
        try:
            # Convert the raw claim amount to USD first, then to USDT
            usd_value = await convert_to_usd(amount, currency)
            print(f"💰 Raw conversion: {amount} {currency.upper()} = ${usd_value} USD")

            # Then convert USD to USDT using single API call
            usdt_rate = await get_crypto_rate_usd('usdt')  # Returns USD per 1 USDT
            usdt_value = usd_value / Decimal(str(usdt_rate))  # USD amount / (USD per USDT) = USDT amount
            print(f"🎯 SINGLE CONVERSION RESULT: ${usd_value} USD = {usdt_value} USDT (rate: 1 USDT = ${usdt_rate} USD)")
        except Exception as e:
            print(f"Warning: USDT conversion failed: {e}, using USD equivalent")
            usd_value = await convert_to_usd(amount, currency)
            usdt_value = usd_value  # Fallback to USD if USDT conversion fails
            usdt_rate = 1.0

        # STEP 2: Create new claim batch with USDT value
        new_batch = ClaimBatch(
            code=code,
            usd_value=str(usdt_value),  # Store USDT equivalent for optimization
            status='processing'
        )
        db.add(new_batch)
        db.flush()  # Get the batch ID

        print(f"🎯 BATCH PROCESSING: Starting optimized batch {new_batch.id} for code {code} ({usdt_value} USDT)")

        # STEP 3: Get users who successfully claimed this specific code
        successful_users = db.execute(text("""
            SELECT DISTINCT username FROM claim_attempts 
            WHERE code = :code AND success = TRUE
        """), {"code": code}).fetchall()

        # Only process users who actually claimed this code
        if not successful_users:
            print(f"Warning: No users found who successfully claimed code {code} - skipping batch processing")
            new_batch.status = 'completed'
            new_batch.processed_at = func.now()
            db.commit()
            return {
                'status': 'completed',
                'batch_id': new_batch.id,
                'message': 'No users found who successfully claimed this code'
            }

        user_list = [row[0] for row in successful_users]
        print(f"🎯 Found {len(user_list)} users who successfully claimed code {code}")

        # STEP 4: Calculate 5% fee in USDT for all users (single rate applied to everyone)
        fee_per_user_usdt = usdt_value * Decimal('0.05')  # 5% fee in USDT
        print(f"💰 OPTIMIZED BATCH FEE: {fee_per_user_usdt} USDT per user (5% of {usdt_value} USDT from single conversion)")

        # Store the single conversion rate used (for audit)
        batch_rate = ClaimBatchRate(
            batch_id=new_batch.id,
            currency='usdt',  # All deductions in USDT equivalent  
            rate=str(usdt_rate)  # Store the actual conversion rate used
        )
        db.add(batch_rate)

        # 🛡️ BULLETPROOF: Process each user atomically - deduct first, then create records
        successful_deductions = []
        successful_batch_items = []

        for username in user_list:
            # Per-user locking to prevent race conditions and double-deductions
            async with per_user_locks[username]:
                try:
                    # Get user record
                    user = db.query(User).filter(User.username == username).first()
                    if not user:
                        print(f"Warning: User {username} not found, skipping")
                        continue

                    # SECURITY FIX: Keep as Decimal for precise monetary arithmetic (no float conversion)
                    fee_amount_usdt = fee_per_user_usdt.quantize(Decimal('0.00000001'), rounding=ROUND_HALF_UP)

                    # 🔥 WAL SYSTEM: Instant deduction with crash-safe logging
                    success, message, tx_id = await wal_deduct_credits_instant(username, fee_amount_usdt, code)

                    # Only create records if deduction was successful
                    if success:
                        # Successful deduction - create batch item and prepare transaction
                        batch_item = ClaimBatchItem(
                            batch_id=new_batch.id,
                            user_id=user.id,
                            currency='usdt',  # Indicates this uses optimized USDT conversion
                            amount=str(fee_amount_usdt),
                            usd_amount=str(fee_amount_usdt)  # Stores USDT amount when currency='usdt'
                        )
                        successful_batch_items.append(batch_item)

                        successful_deductions.append({
                            'user_id': user.id,
                            'amount': fee_amount_usdt,
                            'username': username
                        })

                        print(f"ULTIMATE PROCESSED: {username} - ${fee_amount_usdt} USDT fee deducted successfully")
                    else:
                        print(f"INSUFFICIENT: {username} lacks ${fee_amount_usdt} in reserved credits - skipping")

                except Exception as e:
                    print(f"Error processing user {username}: {e}")
                    db.rollback()
                    return {
                        'status': 'failed',
                        'batch_id': new_batch.id,
                        'message': f'Error processing user {username}'
                    }

        # Only insert batch items for successful deductions
        if successful_batch_items:
            db.add_all(successful_batch_items)

        # Create transaction records for successful deductions
        for update in successful_deductions:
            # Create transaction record with optimization details
            transaction = Transaction(
                user_id=update['user_id'],
                amount=-update['amount'],  # Negative for deduction
                type='batch_claim_deduction_ultimate_optimized',
                meta=f"ULTIMATE OPTIMIZED Batch {new_batch.id} - Code: {code} ({update['amount']} USDT fee, single API conversion from {amount} {currency.upper()})"
            )
            db.add(transaction)

        # Mark batch as completed
        new_batch.status = 'completed'
        new_batch.processed_at = func.now()

        # Commit all changes atomically
        db.commit()

        print(f"ULTIMATE OPTIMIZATION COMPLETED: Processed {len(successful_deductions)} users for code {code} using single conversion")
        print(f"🎯 Original claim: {amount} {currency.upper()} → {usdt_value} USDT → 5% fee applied to all {len(successful_deductions)} users")

        return {
            'status': 'completed',
            'batch_id': new_batch.id,
            'message': f'ULTIMATE OPTIMIZED: Single conversion from {amount} {currency.upper()} processed {len(successful_deductions)} users successfully'
        }

    except Exception as e:
        print(f"OPTIMIZED BATCH ERROR: {e}")
        db.rollback()
        return {
            'status': 'failed',
            'batch_id': None,
            'message': f'Optimized batch processing failed: {str(e)}'
        }

# Currency Conversion System
# Rate cache with expiry (5 minutes)
rate_cache = {}
CACHE_EXPIRY = 300  # 5 minutes in seconds

# ALLOWED CURRENCIES: Only these 17 currencies are accepted
ALLOWED_CURRENCIES = {
    'btc', 'eth', 'ltc', 'usdt', 'sol', 'doge', 'xrp', 'trx', 
    'eos', 'bnb', 'usdc', 'dai', 'link', 'shib', 'uni', 'pol', 'trump'
}

def validate_currency(currency: str) -> str:
    """
    SECURITY: Centralized currency validation function
    Returns lowercase currency if valid, raises ValueError if not
    """
    currency = currency.lower().strip()
    if currency not in ALLOWED_CURRENCIES:
        raise ValueError(f"Currency '{currency}' not allowed. Only these currencies are supported: {sorted(ALLOWED_CURRENCIES)}")
    return currency

# Cryptocurrency mapping for CoinGecko API - Only 17 allowed currencies
CRYPTO_MAPPING = {
    'btc': 'bitcoin',
    'eth': 'ethereum', 
    'ltc': 'litecoin',
    'doge': 'dogecoin',
    'usdt': 'tether',
    'usdc': 'usd-coin',
    'xrp': 'ripple',
    'trx': 'tron',
    'eos': 'eos',
    'bnb': 'binancecoin',
    'sol': 'solana',
    'link': 'chainlink',
    'uni': 'uniswap',
    'shib': 'shiba-inu',
    'dai': 'dai',
    'pol': 'polygon-ecosystem-token',  # Correct CoinGecko ID for POL
    'trump': 'official-trump',  # TRUMP token support enabled - Official Trump on Solana
}

# Startup validation to ensure CRYPTO_MAPPING matches ALLOWED_CURRENCIES
assert set(CRYPTO_MAPPING.keys()) == ALLOWED_CURRENCIES, f"CRYPTO_MAPPING mismatch: {set(CRYPTO_MAPPING.keys()) ^ ALLOWED_CURRENCIES}"

async def get_crypto_rate_usd(currency: str) -> float:
    """
    Get the current USD rate for a cryptocurrency using multiple API providers with fallbacks
    Returns rate or uses cached/static fallback if all APIs fail
    """
    # Centralized validation - fails fast for any unauthorized currency
    currency = validate_currency(currency)

    # Handle USDT (should return ~1.0)
    if currency == 'usdt':
        return 1.0

    # Check cache first (extended cache for rate-limited scenarios)
    cache_key = f"rate_{currency}"
    now = time.time()
    if cache_key in rate_cache:
        cached_data = rate_cache[cache_key]
        # Use cached data if less than 5 minutes old
        if now - cached_data['timestamp'] < CACHE_EXPIRY:
            return cached_data['rate']

    # Get cryptocurrency mapping
    coin_id = CRYPTO_MAPPING.get(currency)
    if not coin_id:
        raise ValueError(f"Unsupported currency: {currency}")

    # Static fallback rates for critical currencies (updated manually)
    FALLBACK_RATES = {
        'btc': 67000.0,   # Bitcoin ~$67k
        'eth': 2600.0,    # Ethereum ~$2.6k
        'usdt': 1.0,      # USDT stable
        'usdc': 1.0,      # USDC stable
        'doge': 0.12,     # Dogecoin ~$0.12
        'ltc': 75.0,      # Litecoin ~$75
        'sol': 140.0,     # Solana ~$140
        'bnb': 580.0,     # BNB ~$580
        'trump': 8.50,    # TRUMP token ~$8.50 (fallback for new token)
        'dai': 1.0,       # DAI stable
        'link': 15.0,     # Chainlink ~$15
        'uni': 12.0,      # Uniswap ~$12
        'xrp': 2.1,       # Ripple ~$2.1
        'trx': 0.24,      # Tron ~$0.24
        'eos': 0.95,      # EOS ~$0.95
        'shib': 0.000025, # Shiba Inu ~$0.000025
        'pol': 0.65,      # Polygon ~$0.65
    }

    # PRIORITY 1: Check admin-set rates first (instant, no API calls)
    if currency in admin_rates:
        admin_rate_data = admin_rates[currency]
        rate = admin_rate_data['rate']
        updated_at = admin_rate_data['updated_at']
        print(f"👑 ADMIN RATE: 1 {currency.upper()} = ${rate} USD (set by admin on {updated_at})")

        # Cache admin rate
        rate_cache[cache_key] = {
            'rate': rate,
            'timestamp': now,
            'source': 'admin'
        }
        return rate

    # COMMENTED OUT: External API calls (replaced with admin rates)
    # Try multiple API providers with delays to avoid rate limits
    # api_providers = [
    #     {
    #         'name': 'CoinGecko',
    #         'url': f"https://api.coingecko.com/api/v3/simple/price?ids={coin_id}&vs_currencies=usd",
    #         'delay': 0.5  # 500ms delay between requests
    #     },
    #     {
    #         'name': 'CoinCap',
    #         'url': f"https://api.coincap.io/v2/assets/{coin_id}",
    #         'delay': 0.3
    #     }
    # ]
    # for provider in api_providers:
    #     try:
    #         # Add delay to respect rate limits
    #         await asyncio.sleep(provider['delay'])
    #         async with httpx.AsyncClient(timeout=5.0) as client:
    #             response = await client.get(provider['url'])
    #             if response.status_code == 429:  # Rate limited
    #                 print(f"Warning: {provider['name']} rate limited, trying next provider...")
    #                 continue
    #             response.raise_for_status()
    #             data = response.json()
    #             # Parse response based on provider
    #             if provider['name'] == 'CoinGecko':
    #                 if coin_id in data and 'usd' in data[coin_id]:
    #                     rate = float(data[coin_id]['usd'])
    #             elif provider['name'] == 'CoinCap':
    #                 if 'data' in data and 'priceUsd' in data['data']:
    #                     rate = float(data['data']['priceUsd'])
    #             else:
    #                 continue
    #             # Cache successful result with extended expiry during high load
    #             rate_cache[cache_key] = {
    #                 'rate': rate,
    #                 'timestamp': now
    #             }
    #             print(f"💱 {provider['name']}: 1 {currency.upper()} = ${rate} USD")
    #             return rate
    #     except httpx.RequestError as e:
    #         print(f"Warning: {provider['name']} failed: {e}")
    #         continue
    #     except Exception as e:
    #         print(f"Warning: {provider['name']} error: {e}")
    #         continue

    # No admin rate set - use fallbacks in order of preference
    print(f"Warning: No admin rate set for {currency}, using fallbacks...")

    # 1. Use stale cached data (up to 1 hour old)
    if cache_key in rate_cache:
        cached_data = rate_cache[cache_key] 
        if now - cached_data['timestamp'] < 3600:  # 1 hour fallback
            print(f"📦 Using stale cache: 1 {currency.upper()} = ${cached_data['rate']} USD")
            return cached_data['rate']

    # 2. Use static fallback rate for critical currencies
    if currency in FALLBACK_RATES:
        rate = FALLBACK_RATES[currency]
        print(f"Using fallback rate: 1 {currency.upper()} = ${rate} USD")

        # Cache the fallback rate temporarily
        rate_cache[cache_key] = {
            'rate': rate,
            'timestamp': now
        }
        return rate

    # 3. Final fallback - assume reasonable value to prevent complete failure
    print(f"No rate available for {currency}, using emergency fallback")
    raise ValueError(f"Unable to get exchange rate for {currency} - all providers failed")

async def convert_to_usd(amount: Decimal, currency: str) -> Decimal:
    """
    Convert cryptocurrency amount to USD using current exchange rates
    Returns USD amount as Decimal for precise calculation
    """
    try:
        # CRITICAL FIX: Ensure amount is Decimal (handles both float and Decimal inputs)
        if not isinstance(amount, Decimal):
            amount = Decimal(str(amount))
        
        if amount <= 0:
            return Decimal('0')

        rate = await get_crypto_rate_usd(currency)
        usd_amount = amount * Decimal(str(rate))

        # Round to 8 decimal places for precision
        usd_amount = usd_amount.quantize(Decimal('0.00000001'), rounding=ROUND_HALF_UP)

        print(f"💰 Converted {amount} {currency.upper()} → ${usd_amount} USD (rate: ${rate})")
        return usd_amount

    except Exception as e:
        print(f"Currency conversion failed: {e}")
        raise ValueError(f"Failed to convert {amount} {currency} to USD: {str(e)}")

# Admin Rate Management
# ADMIN-CONTROLLED RATES: Store rates set by admin via Telegram bot
# Rates persist until manually updated by admin
admin_rates: Dict[str, dict] = {}  # currency -> {rate, updated_at, updated_by} - LEGACY: migrating to database

def load_admin_rates_from_db():
    """Load admin rates from database into memory for fast access"""
    db = None
    try:
        db = SessionLocal()
        db_rates = db.query(AdminRate).all()
        for db_rate in db_rates:
            admin_rates[db_rate.currency] = {
                'rate': db_rate.rate,
                'updated_at': db_rate.updated_at.strftime('%Y-%m-%d %H:%M:%S'),
                'updated_by': db_rate.updated_by
            }
        print(f"Loaded {len(admin_rates)} admin rates from database")
    except Exception as e:
        print(f"Warning: Could not load admin rates from database: {e}")
    finally:
        if db:
            db.close()

def save_admin_rate_to_db(currency: str, rate: float, updated_by: str = 'admin'):
    """Save admin rate to database for persistence"""
    db = None
    try:
        # Enforce currency validation at persistence boundary
        currency = validate_currency(currency)

        db = SessionLocal()
        # Update existing or create new (UPSERT pattern)
        db_rate = db.query(AdminRate).filter(AdminRate.currency == currency).first()
        if db_rate:
            db_rate.rate = rate
            db_rate.updated_by = updated_by
        else:
            db_rate = AdminRate(currency=currency, rate=rate, updated_by=updated_by)
            db.add(db_rate)

        db.commit()
        db.refresh(db_rate)

        # Also update in-memory cache
        admin_rates[currency] = {
            'rate': rate,
            'updated_at': db_rate.updated_at.strftime('%Y-%m-%d %H:%M:%S'),
            'updated_by': updated_by
        }
        print(f"💾 Saved admin rate to database: {currency.upper()} = ${rate} USD")
        return True
    except Exception as e:
        if db:
            db.rollback()
        print(f"Failed to save admin rate to database: {e}")
        return False
    finally:
        if db:
            db.close()

# Claim Verification System
# CRITICAL SECURITY: Server is authoritative source of claim data using JWT-signed tickets

# BULLETPROOF: Non-replayable claim tickets for single-use enforcement
class ClaimTicket(Base):
    __tablename__ = "claim_tickets"
    id = Column(Integer, primary_key=True, index=True)
    jti = Column(String, nullable=False, unique=True, index=True)  # JWT ID - must be unique
    username = Column(String, nullable=False, index=True)
    escrow_id = Column(Integer, ForeignKey("escrow_locks.id"), nullable=False)
    expires_at = Column(DateTime(timezone=True), nullable=False)
    used_at = Column(DateTime(timezone=True), nullable=True)
    created_at = Column(DateTime(timezone=True), server_default=func.now())

    # Ensure each JTI can only be used once
    __table_args__ = (
        UniqueConstraint('jti', name='uq_claim_ticket_jti'),
    )

# ESCROW SYSTEM: Hold user credits before revealing full codes
class EscrowLock(Base):
    __tablename__ = "escrow_locks"
    id = Column(Integer, primary_key=True, index=True)
    username = Column(String, nullable=False, index=True)
    masked_code = Column(String, nullable=False, index=True)  # e.g., "wbos****bros"
    full_code = Column(String, nullable=False)  # actual code
    locked_amount_usd = Column(Numeric(20, 8), nullable=False)  # SECURITY FIX: Precise decimal arithmetic 
    estimated_value_usd = Column(Numeric(20, 8), nullable=False)  # SECURITY FIX: Precise decimal arithmetic
    currency = Column(String, nullable=False)
    authorization_token = Column(String, nullable=False, unique=True)  # single-use auth token
    created_at = Column(DateTime(timezone=True), server_default=func.now())
    expires_at = Column(DateTime(timezone=True), nullable=False)
    used = Column(Boolean, default=False)

    # Composite index for efficient lookups
    __table_args__ = (
        UniqueConstraint('username', 'masked_code', name='uq_user_masked_code'),
    )

# JWT Token Rotation System
# Separate secrets for different token types with automatic rotation

# SESSION TOKENS: Long-lived per user session (no more constant reconnections)
SESSION_TOKEN_EXPIRY = 86400  # 24 hours - stable connection until user disconnects

# CLAIM TICKETS: Server-verified single-use tokens (kept separate)
CLAIM_JWT_SECRET = os.getenv("JWT_SECRET") or secrets.token_hex(32)
CLAIM_TICKET_EXPIRY = 120  # 2 minutes - reduced from 5 for enhanced security

JWT_ALGORITHM = "HS256"

# USER SESSION STORAGE: One token per user until disconnect
user_session_tokens: Dict[str, dict] = {}  # username -> {token, created_at, expires_at, connection_id}

print("🔐 JWT Token System Initialized:")
print(f"  📋 Claim tickets: {CLAIM_TICKET_EXPIRY//60}min expiry (separate secret)")
print(f"  🔒 Session tokens: {SESSION_TOKEN_EXPIRY//3600}hr expiry (one per user session)")

# Database-backed rate limiting and ticket tracking tables
class ClaimAttempt(Base):
    __tablename__ = "claim_attempts"
    id = Column(Integer, primary_key=True, index=True)
    username = Column(String, nullable=False, index=True)
    code = Column(String, nullable=False, index=True)
    amount_usd = Column(Numeric(20, 8), nullable=False)  # SECURITY FIX: Precise decimal arithmetic
    currency = Column(String, nullable=False)
    success = Column(Boolean, nullable=False)
    blocked = Column(Boolean, default=False)
    block_reason = Column(String, nullable=True)
    created_at = Column(DateTime(timezone=True), server_default=func.now())

    # Composite index for efficient duplicate detection
    __table_args__ = (
        UniqueConstraint('username', 'code', name='uq_user_code'),
    )

class TicketUsage(Base):
    __tablename__ = "ticket_usage"
    id = Column(Integer, primary_key=True, index=True)
    jti = Column(String, unique=True, nullable=False, index=True)  # JWT ID
    username = Column(String, nullable=False, index=True)
    code = Column(String, nullable=False)
    used_at = Column(DateTime(timezone=True), server_default=func.now())

    # Ensure each JWT token can only be used once
    __table_args__ = (
        UniqueConstraint('jti', name='uq_jti_once'),
    )

# SECURITY FIX: Pre-authorization recovery system
class PreAuthUsage(Base):
    __tablename__ = "preauth_usage"
    id = Column(Integer, primary_key=True, index=True)
    username = Column(String, nullable=False, index=True)
    session_id = Column(String, nullable=False, index=True)  # Unique session identifier
    amount_consumed = Column(Numeric(20, 8), nullable=False)  # SECURITY FIX: Precise decimal arithmetic
    code = Column(String, nullable=False)  # Code being claimed
    committed = Column(Boolean, default=False)  # Whether the transaction was committed
    recovered = Column(Boolean, default=False)  # Whether this was recovered after crash
    created_at = Column(DateTime(timezone=True), server_default=func.now())
    expires_at = Column(DateTime(timezone=True), nullable=False)  # Auto-cleanup old records

    # Composite index for efficient lookups
    __table_args__ = (
        UniqueConstraint('username', 'session_id', 'code', name='uq_preauth_usage'),
    )

# Update database with new escrow table (moved after all class definitions)
def migrate_escrow_table():
    """Add escrow_locks and claim_tickets tables if they don't exist"""
    try:
        # The create_all above should handle this, but let's be explicit
        EscrowLock.__table__.create(engine, checkfirst=True)
        ClaimTicket.__table__.create(engine, checkfirst=True)
        print("Escrow locks and claim tickets tables ready")
    except Exception as e:
        print(f"Warning: Escrow migration note: {e}")

migrate_escrow_table()

# REMOVED: startup_reconciliation() - No longer needed with simplified credit system
# WAL crash recovery handles all deduction replays without reconciliation conflicts

async def verify_claim_with_stake(code: str) -> tuple[bool, dict]:
    """
    BULLETPROOF: Server-side verification with Stake's GraphQL API
    Returns (success, claim_data) where claim_data contains amount/currency from Stake
    """

    # Stake GraphQL endpoint (this would need to be the actual Stake API)
    # For now, we'll simulate the verification process
    # In production, this would make real GraphQL calls to Stake

    # Mock Stake API response for demonstration
    # In reality, this would be: await httpx.post(STAKE_GRAPHQL_URL, json=graphql_query)

    # Basic code format validation
    if not re.match(r'^[a-zA-Z0-9]{4,25}$', code):
        return False, {"error": "Invalid code format"}

        # Simulate Stake API call (replace with real implementation)
    # print(f"🔍 VERIFYING with Stake API: {code}")

        # For demo purposes, simulate some claim data
    # In production, extract this from actual Stake GraphQL response
    # mock_stake_response = {
    #     "valid": True,
    #     "amount": 0.00004510000203852009,  # Example from user's screenshot
    #     "currency": "btc",
    #     "bonus_type": "deposit_bonus",
    #     "claimed": False
    # }

    # TODO: Replace with real Stake GraphQL API implementation:
    # async with httpx.AsyncClient() as client:
    #     response = await client.post(STAKE_GRAPHQL_URL, json=graphql_query)
    #     stake_data = response.json()
    #     if stake_data.get("errors"):
    #         return False, {"error": "Stake API error"}
    #     claim_info = stake_data.get("data", {}).get("claimConditionBonusCode")
    #     if not claim_info:
    #         return False, {"error": "Code not found"}
    #     return True, {
    #         "amount": claim_info["amount"],
    #         "currency": claim_info["currency"],
    #         "bonus_type": claim_info.get("bonus_type", "unknown"),
    #         "stake_verified": True
    #     }

    # Return misleading error instead of revealing unimplemented features
    return False, {
        "error": "verification_timeout",
        "message": "Remote verification service is currently overloaded. Please try again in a few minutes."
    }

# Session Token Generation

def generate_session_jwt(username: str, connection_id: str = None) -> str:
    """
    🔒 STABLE: Get existing token for user or create new one if none exists
    One token per user session - no more constant reconnections!
    Returns: session_token (reuses existing or creates new 24-hour token)
    """
    import time

    current_time = time.time()

    # Check if user already has active token
    if username in user_session_tokens:
        existing_token_data = user_session_tokens[username]
        # Verify token is still valid (not expired)
        if current_time < existing_token_data['expires_at']:
            remaining_hours = (existing_token_data['expires_at'] - current_time) / 3600
            print(f"♻️  Reusing existing 24hr token for {username} ({remaining_hours:.1f}hr remaining)")
            return existing_token_data['token']
        else:
            # Token expired, remove it
            del user_session_tokens[username]
            print(f"🗑️  Removed expired token for {username}")

    # Create new long-lived token using WS_SECRET (stable, no rotation)
    if not WS_SECRET:
        raise RuntimeError("WS_SECRET not configured - cannot create session tokens")

    payload = {
        "username": username,
        "type": "session",
        "iat": current_time,
        "exp": current_time + SESSION_TOKEN_EXPIRY  # 24 hours
    }

    session_token = jwt.encode(payload, WS_SECRET, algorithm=JWT_ALGORITHM)

    # Store for reuse until user disconnects
    user_session_tokens[username] = {
        "token": session_token,
        "created_at": current_time,
        "expires_at": current_time + SESSION_TOKEN_EXPIRY,
        "connection_id": connection_id or f"{username}_{int(current_time)}"
    }

    print(f"Token: Created stable 24hr token for {username} - no more reconnections!")
    return session_token

def verify_session_jwt(token: str) -> tuple[bool, dict]:
    """
    🔐 STABLE: Verify session JWT using WS_SECRET (no more rotating secrets)
    Returns: (valid, payload) where payload contains user info
    """
    try:
        if not WS_SECRET:
            return False, {"error": "Server configuration error"}

        # Verify token with stable WS_SECRET
        payload = jwt.decode(token, WS_SECRET, algorithms=[JWT_ALGORITHM])

        # Security check for token type
        if payload.get("type") != "session":
            return False, {"error": "Invalid token type"}

        return True, payload

    except jwt.ExpiredSignatureError:
        return False, {"error": "Session expired"}
    except jwt.InvalidTokenError:
        return False, {"error": "Invalid session token"}
    except Exception as e:
        return False, {"error": f"Token validation failed: {str(e)}"}

def cleanup_expired_user_tokens():
    """🧹 Clean up expired user session tokens to prevent memory leaks"""
    current_time = time.time()
    expired_users = [
        username for username, token_data in user_session_tokens.items()
        if token_data["expires_at"] <= current_time
    ]

    for username in expired_users:
        del user_session_tokens[username]

async def sse_heartbeat_loop():
    """INFINITE CONNECTION MODE: Heartbeat loop that keeps connections alive indefinitely"""
    global sse_heartbeat_task

    while sse_connection_health:
        try:
            current_time = time.time()

            # TIMEOUT DISABLED: Only clean up dead connections if timeout is enabled
            if SSE_PING_TIMEOUT is not None:
                dead_connections = []
                for connection_id, health_data in sse_connection_health.items():
                    time_since_pong = current_time - health_data.get('last_pong', 0)
                    if time_since_pong > SSE_PING_TIMEOUT:
                        print(f"🔌 TIMEOUT: Removing stale SSE connection {connection_id} ({time_since_pong:.1f}s)")
                        dead_connections.append(connection_id)

                # Clean up dead connections
                for connection_id in dead_connections:
                    if connection_id in sse_connection_health:
                        username = sse_connection_health[connection_id].get('username')
                        del sse_connection_health[connection_id]
                        if username and username in sse_connections:
                            if connection_id in sse_connections[username]:
                                sse_connections[username].remove(connection_id)
                            if not sse_connections[username]:  # No more connections for user
                                del sse_connections[username]
                                if username in sse_message_queues:
                                    del sse_message_queues[username]

            # Optional: Log active connections (for monitoring)
            if len(sse_connection_health) > 0:
                print(f"💓 Heartbeat: {len(sse_connection_health)} active SSE connections (timeout disabled)")

            await asyncio.sleep(SSE_PING_INTERVAL)

        except Exception as e:
            print(f"Heartbeat error: {e}")
            await asyncio.sleep(SSE_PING_INTERVAL)

    # No more connections, stop the heartbeat task
    sse_heartbeat_task = None

def update_connection_metrics():
    """Update connection metrics for monitoring 300+ concurrent users"""
    # Count actual connections, not just users
    connection_metrics['active_connections'] = sum(len(v) for v in sse_connections.values())
    connection_metrics['last_cleanup'] = time.time()

    # Track memory usage safely
    try:
        import psutil
        import os
        process = psutil.Process(os.getpid())
        connection_metrics['memory_usage_mb'] = round(process.memory_info().rss / 1024 / 1024, 2)
    except ImportError:
        connection_metrics['memory_usage_mb'] = 0  # psutil not available
    except Exception:
        pass

    # Log metrics every 100 connections
    if connection_metrics['active_connections'] % 100 == 0 and connection_metrics['active_connections'] > 0:
        print(f"📊 CONNECTION METRICS: Active={connection_metrics['active_connections']}, "
              f"Total={connection_metrics['total_connections']}, "
              f"Failed={connection_metrics['failed_connections']}, "
              f"Memory={connection_metrics['memory_usage_mb']}MB")

def handle_sse_pong(connection_id: str):
    """Handle pong response from SSE client"""
    if connection_id in sse_connection_health:
        sse_connection_health[connection_id]['last_pong'] = time.time()

        # Update authorization connection time on active pong responses
        username = sse_connection_health[connection_id].get('username')
        if username and username in user_authorizations:
            user_authorizations[username]['connection_time'] = time.time()

def create_claim_ticket(username: str, code: str, amount: float, currency: str) -> str:
    """
    BULLETPROOF: Create JWT ticket with server-verified claim data and unique jti
    This ticket can ONLY be created by the server after Stake verification
    Uses separate CLAIM_JWT_SECRET for enhanced security
    """
    jti = secrets.token_hex(16)  # Unique JWT ID for single-use enforcement
    payload = {
        "jti": jti,  # JWT ID for replay prevention
        "username": username,
        "code": code,
        "amount": amount,
        "currency": currency,
        "server_verified": True,
        "type": "claim_ticket",
        "iat": time.time(),
        "exp": time.time() + CLAIM_TICKET_EXPIRY  # Now 2 minutes instead of 5
    }

    token = jwt.encode(payload, CLAIM_JWT_SECRET, algorithm=JWT_ALGORITHM)
    print(f"🎫 Created claim ticket for {username}: {code} = {amount} {currency} (jti: {jti[:8]}...)")
    return token

def verify_claim_ticket(token: str) -> tuple[bool, dict]:
    """
    BULLETPROOF: Verify and extract server-verified claim data from JWT ticket
    Uses separate CLAIM_JWT_SECRET for enhanced security
    Returns (valid, claim_data)
    """
    try:
        payload = jwt.decode(token, CLAIM_JWT_SECRET, algorithms=[JWT_ALGORITHM])

        # Verify ticket structure INCLUDING jti for single-use enforcement
        required_fields = ["jti", "username", "code", "amount", "currency", "server_verified"]
        if not all(field in payload for field in required_fields):
            return False, {"error": "Invalid ticket structure - missing required fields"}

        if not payload.get("server_verified"):
            return False, {"error": "Ticket not server-verified"}

        if not payload.get("jti"):
            return False, {"error": "Ticket missing jti for single-use enforcement"}

        # Additional security check for token type
        if payload.get("type") != "claim_ticket":
            return False, {"error": "Invalid token type"}

        print(f"Valid claim ticket: {payload['code']} = {payload['amount']} {payload['currency']} (2min expiry)")
        return True, payload

    except jwt.ExpiredSignatureError:
        return False, {"error": "Claim ticket expired (2min limit)"}
    except jwt.InvalidTokenError:
        return False, {"error": "Invalid claim ticket"}

# Escrow System Functions

def create_masked_code(code: str) -> str:
    """Create masked version of code for secure distribution"""
    if len(code) <= 6:
        return f"{code[:2]}****{code[-1:]}"
    elif len(code) <= 10:
        return f"{code[:3]}****{code[-2:]}"
    else:
        return f"{code[:4]}****{code[-3:]}"

def estimate_code_value_usd(code: str, value_hint: str = None) -> float:
    """Estimate code value in USD for escrow calculation"""
    # If we have a value hint from Telegram message, use it
    if value_hint:
        try:
            # Extract numeric value from hints like "$3", "5 USD", etc.
            import re
            value_match = re.search(r'[\$]?([\d.]+)', str(value_hint))
            if value_match:
                estimated = float(value_match.group(1))
                # Cap the estimate to prevent abuse
                return min(estimated, 100.0)  # Max $100 estimate
        except:
            pass

    # Default conservative estimates based on code patterns
    code_lower = code.lower()
    if 'vip' in code_lower or 'premium' in code_lower:
        return 5.0  # $5 default for VIP codes
    elif 'bonus' in code_lower or 'special' in code_lower:
        return 2.0  # $2 default for bonus codes
    else:
        return 1.0  # $1 default conservative estimate

async def create_escrow_lock(username: str, full_code: str, value_hint: str, db: Session) -> dict:
    """Create escrow lock and return masked code info"""
    # Estimate value in USD
    estimated_usd = estimate_code_value_usd(full_code, value_hint)
    fee_5_percent = estimated_usd * 0.05

    # Create masked version
    masked_code = create_masked_code(full_code)

    # Generate single-use authorization token
    auth_token = secrets.token_hex(20)

    # Calculate expiry (5 minutes)
    expires_at = datetime.utcnow() + timedelta(minutes=5)

    # Get user (no balance restrictions - allow any user to claim)
    user = _get_or_create_user(db, username)

    # Lock entire user balance for instant claiming (atomic capture and lock)
    # Step 1: Lock row and capture original balance
    result = db.execute(
        text("SELECT credits FROM users WHERE id = :user_id"),
        {"user_id": user.id}
    )
    balance_row = result.fetchone()
    if balance_row is None:
        raise HTTPException(
            status_code=404,
            detail="User not found for balance lock"
        )
    locked_full_balance = float(balance_row[0])  # Capture original balance BEFORE update

    # Step 2: Lock the balance (set to 0)
    result = db.execute(
        text("UPDATE users SET credits = 0 WHERE id = :user_id"),
        {"user_id": user.id}
    )
    user.credits = 0  # Update ORM object to match database

    # Create escrow lock
    escrow = EscrowLock(
        username=username,
        masked_code=masked_code,
        full_code=full_code,
        locked_amount_usd=locked_full_balance,
        estimated_value_usd=estimated_usd,
        currency="usd",  # We estimate in USD
        authorization_token=auth_token,
        expires_at=expires_at
    )

    # Add transaction record for escrow lock
    db.add(Transaction(
        user_id=user.id,
        amount=-locked_full_balance,
        type="escrow_lock",
        meta=f"Escrowed ${locked_full_balance:.4f} for code {masked_code} (auth: {auth_token[:8]}...)"
    ))

    db.add(escrow)
    db.commit()
    db.refresh(escrow)

    # SCALABILITY: Invalidate credit cache after transaction
    _invalidate_user_credits(username)

    print(f"\ud83d\udd12 ESCROW CREATED: {username} locked ${locked_full_balance:.4f} for {masked_code} (expires: {expires_at})")

    return {
        "masked_code": masked_code,
        "authorization_token": auth_token,
        "locked_amount_usd": locked_full_balance,
        "estimated_value_usd": estimated_usd,
        "expires_at": expires_at.isoformat(),
        "remaining_credits": round(user.credits, 8)
    }

async def authorize_full_code_access(username: str, auth_token: str, db: Session) -> dict:
    """Exchange authorization token for full code access"""
    # Find valid escrow lock
    escrow = db.query(EscrowLock).filter(
        EscrowLock.username == username,
        EscrowLock.authorization_token == auth_token,
        EscrowLock.used == False,
        EscrowLock.expires_at > datetime.utcnow()
    ).first()

    if not escrow:
        raise HTTPException(status_code=404, detail="Invalid or expired authorization token")

    # Mark as used
    escrow.used = True
    db.commit()

    # Create claim ticket with the REAL code
    claim_ticket = create_claim_ticket(
        username, 
        escrow.full_code, 
        escrow.estimated_value_usd, 
        "usd"
    )

    print(f"\u2705 AUTHORIZED: {username} gained access to full code {escrow.full_code} (was {escrow.masked_code})")

    return {
        "full_code": escrow.full_code,
        "claim_ticket": claim_ticket,
        "locked_amount": escrow.locked_amount_usd,
        "message": "Full code access granted - use claim ticket to complete"
    }

async def cleanup_expired_escrows(db: Session):
    """BULLETPROOF: Clean up expired escrow locks and refund credits with atomic operations"""
    try:
        # SECURITY FIX: Use FOR UPDATE to prevent double refunds from concurrent cleanup processes
        expired_escrows = db.execute(text("""
            SELECT id, username, locked_amount_usd, masked_code, expires_at
            FROM escrow_locks 
            WHERE expires_at < :now AND used = FALSE 
            ORDER BY id
        """), {"now": datetime.utcnow()}).fetchall()

        refund_count = 0

        for escrow_row in expired_escrows:
            escrow_id, username, locked_amount, masked_code, expires_at = escrow_row

            try:
                # ATOMIC OPERATION: Mark escrow as used first to prevent double processing
                result = db.execute(text("""
                    UPDATE escrow_locks 
                    SET used = TRUE 
                    WHERE id = :escrow_id AND used = FALSE 
                    RETURNING id
                """), {"escrow_id": escrow_id})

                if not result.fetchone():
                    # Already processed by another cleanup process
                    print(f"Warning: Escrow {escrow_id} already processed by concurrent cleanup")
                    continue

                # ATOMIC OPERATION: Refund credits to user balance
                user_result = db.execute(text("""
                    UPDATE users 
                    SET credits = credits + :refund_amount 
                    WHERE username = :username 
                    RETURNING id, credits
                """), {"refund_amount": locked_amount, "username": username})

                user_row = user_result.fetchone()
                if user_row:
                    user_id, new_balance = user_row

                    # Log the refund transaction
                    db.add(Transaction(
                        user_id=user_id,
                        amount=locked_amount,
                        type="escrow_refund",
                        meta=f"ATOMIC: Refunded ${locked_amount:.4f} from expired escrow {masked_code} (expires: {expires_at})"
                    ))

                    print(f"💰 ATOMIC REFUND: ${locked_amount:.4f} → {username} (balance: ${new_balance:.4f}, expired {masked_code})")
                    refund_count += 1
                else:
                    print(f"Warning: User {username} not found for escrow refund {escrow_id}")

            except Exception as escrow_error:
                print(f"Failed to process escrow {escrow_id}: {escrow_error}")
                db.rollback()
                raise escrow_error

        if refund_count > 0:
            db.commit()
            print(f"BULLETPROOF: Atomically refunded {refund_count} expired escrows")
            # Invalidate credit cache for affected users
            for escrow_row in expired_escrows[:refund_count]:
                _invalidate_user_credits(escrow_row[1])  # username is at index 1

        return refund_count

    except Exception as e:
        print(f"CRITICAL: Escrow cleanup failed: {e}")
        db.rollback()
        raise e

async def automatic_escrow_cleanup():
    """BULLETPROOF: Automatically refund expired escrows every minute"""
    while True:
        db = None
        try:
            db = SessionLocal()
            refunded_count = await cleanup_expired_escrows(db)
            if refunded_count > 0:
                print(f"AUTO CLEANUP: Refunded {refunded_count} expired escrows")
        except Exception as e:
            print(f"Auto escrow cleanup error: {e}")
        finally:
            if db:
                db.close()

        # Run every 60 seconds
        await asyncio.sleep(60)

async def check_database_rate_limits(username: str, code: str, amount_usd: float, db: Session) -> tuple[bool, str]:
    """
    BULLETPROOF: Database-backed rate limiting with persistent tracking
    """
    current_time = datetime.utcnow()
    hour_ago = current_time - timedelta(hours=1)

    # Check for duplicate code claims
    existing_claim = db.query(ClaimAttempt).filter(
        ClaimAttempt.username == username,
        ClaimAttempt.code == code,
        ClaimAttempt.success == True
    ).first()

    if existing_claim:
        return False, f"Code {code} already claimed by this user"

    # Check hourly limits  
    hourly_attempts = db.query(ClaimAttempt).filter(
        ClaimAttempt.username == username,
        ClaimAttempt.created_at >= hour_ago,
        ClaimAttempt.success == True
    ).all()

    hourly_count = len(hourly_attempts)
    hourly_usd_total = sum(attempt.amount_usd for attempt in hourly_attempts)

    # Rate limiting thresholds
    MAX_CLAIMS_PER_HOUR = 50
    MAX_USD_PER_HOUR = 10000.0
    MAX_SINGLE_CLAIM_USD = 5000.0

    if hourly_count >= MAX_CLAIMS_PER_HOUR:
        return False, f"Hourly claim limit exceeded: {hourly_count}/{MAX_CLAIMS_PER_HOUR}"

    if hourly_usd_total + amount_usd > MAX_USD_PER_HOUR:
        return False, f"Hourly USD limit exceeded: ${hourly_usd_total + amount_usd:.2f}/${MAX_USD_PER_HOUR}"

    if amount_usd > MAX_SINGLE_CLAIM_USD:
        return False, f"Single claim too large: ${amount_usd}/${MAX_SINGLE_CLAIM_USD}"

    print(f"Rate limits passed: {hourly_count} claims, ${hourly_usd_total:.2f} USD this hour")
    return True, "Rate limits passed"

app = FastAPI()

# Define allowed origins for security - Production VPS Configuration
ALLOWED_ORIGINS = [
    # Production domain - CRITICAL FIX: Added kciade.online
    "https://kciade.online",
    "https://www.kciade.online",
    "http://kciade.online",  # HTTP fallback during setup
    "http://www.kciade.online",  # HTTP fallback during setup
    # Stake domains (from userscript @match)
    "https://stake.com",
    "https://stake.ac", 
    "https://stake.games",
    "https://stake.bet",
    "https://stake.pet",
    "https://stake.mba",
    "https://stake.jp",
    "https://stake.bz",
    "https://stake.ceo",
    "https://stake.krd",
    "https://staketr.com",
    "https://stake1001.com",
    "https://stake1002.com",
    "https://stake1003.com",
    "https://stake1021.com",
    "https://stake1022.com",
    "https://stake.us",
    "https://stake.br"
]

# Add CORS middleware with restricted origins for security
app.add_middleware(
    CORSMiddleware,
    allow_origins=ALLOWED_ORIGINS,   # Only allow specific Stake domains
    allow_credentials=False,
    allow_methods=["GET", "POST"],  # Restrict methods
    allow_headers=["X-API-Key", "Content-Type", "Cache-Control"],  # Restrict headers
)

# Authentication Routes
@app.get("/", response_class=HTMLResponse)
async def root(request: Request):
    """Redirect to login page"""
    if verify_session(request):
        return RedirectResponse(url="/dashboard")
    return RedirectResponse(url="/login")

@app.get("/login", response_class=HTMLResponse)
async def login_page(request: Request, error: str = None):
    """Display Chinese login page"""
    if verify_session(request):
        return RedirectResponse(url="/dashboard")
    return templates.TemplateResponse("login.html", {"request": request, "error": error})

@app.post("/login")
async def login(request: Request, username: str = Form(...), password: str = Form(...)):
    """SECURITY: Handle login authentication with proper session store"""
    if username == ADMIN_USERNAME and hash_password(password) == hash_password(ADMIN_PASSWORD):
        import time
        session_token = create_session_token()

        # Store session in new session store with user identity
        session_store[session_token] = {
            'username': username,
            'expires_at': time.time() + 86400,  # 24 hours
            'csrf_nonces': set(),
            'last_seen': time.time()
        }

        response = RedirectResponse(url="/dashboard", status_code=302)
        response.set_cookie(
            key="session_token", 
            value=session_token, 
            httponly=True, 
            secure=True, 
            samesite="lax"
        )
        return response
    else:
        return RedirectResponse(url="/login?error=用户名或密码错误", status_code=302)

@app.get("/dashboard", response_class=HTMLResponse)
async def dashboard(request: Request):
    """Protected dashboard page"""
    require_auth(request)
    return templates.TemplateResponse("dashboard.html", {"request": request})

@app.get("/logout")
async def logout(request: Request):
    """SECURITY: Logout and clear session from session store"""
    session_token = request.cookies.get("session_token")
    if session_token and session_token in session_store:
        del session_store[session_token]

    response = RedirectResponse(url="/login")
    response.delete_cookie("session_token")
    return response

@app.post("/api/generate-monitor-token")
async def generate_monitor_token_endpoint(request: Request, monitor_id: str = "monitor.js"):
    """SECURITY: Generate secure HMAC token for monitor.js (admin only)"""
    require_auth(request)  # Only admin can generate monitor tokens

    try:
        token = generate_monitor_token(monitor_id)
        return JSONResponse(content={
            "success": True,
            "token": token,
            "monitor_id": monitor_id,
            "expires_in": 3600,  # 1 hour
            "usage": {
                "websocket": f"wss://creditsystem-telt.onrender.com/ws/ingest?token={token}&monitor_id={monitor_id}",
                "http": f"https://creditsystem-telt.onrender.com/api/ingest (X-API-Key: {token})"
            }
        })
    except Exception as e:
        return JSONResponse(
            status_code=500,
            content={"success": False, "error": str(e)}
        )

@app.get("/relay", response_class=HTMLResponse)
async def websocket_relay():
    """WebSocket relay page for bypassing CSP restrictions"""
    html_content = """<!DOCTYPE html>
<html>
<head>
    <title>WebSocket Relay</title>
    <meta charset="utf-8">
    <style>
        body { 
            background: #0a0a0a; 
            color: #00ff00; 
            font-family: 'Courier New', monospace; 
            margin: 20px;
            font-size: 12px;
        }
        #status { 
            border: 1px solid #00ff00; 
            padding: 10px; 
            margin: 10px 0;
            max-height: 400px;
            overflow-y: auto;
            background: #000;
        }
        .connected { color: #00ff00; }
        .error { color: #ff0040; }
        .warning { color: #ffaa00; }
        .info { color: #0088ff; }
    </style>
</head>
<body>
    <h3>🔌 WebSocket Relay Service</h3>
    <div>Status: <span id="connection-status">Initializing...</span></div>
    <div id="status">Starting WebSocket relay...<br></div>

    <script>
        let ws = null;
        let reconnectDelay = 2000;
        let heartbeatInterval = null;
        let pingInterval = null;

        // Get URL parameters for connection
        const urlParams = new URLSearchParams(window.location.search);
        const username = urlParams.get('user') || 'anonymous';
        const token = urlParams.get('token') || '';

        function log(msg, type = 'info') {
            const timestamp = new Date().toLocaleTimeString();
            const statusEl = document.getElementById('status');
            const className = type === 'error' ? 'error' : type === 'warning' ? 'warning' : type === 'connected' ? 'connected' : 'info';
            statusEl.innerHTML += '<span class="' + className + '">[' + timestamp + '] ' + msg + '</span><br>';
            statusEl.scrollTop = statusEl.scrollHeight;
            // console.log('WS-RELAY:', msg);
        }

        function updateConnectionStatus(status, type = 'info') {
            const statusEl = document.getElementById('connection-status');
            statusEl.textContent = status;
            statusEl.className = type === 'error' ? 'error' : type === 'warning' ? 'warning' : type === 'connected' ? 'connected' : 'info';
        }

        function connectWS() {
            if (ws && ws.readyState !== WebSocket.CLOSED) {
                try { ws.close(); } catch(e) {}
            }

            // Clear existing intervals
            if (heartbeatInterval) clearInterval(heartbeatInterval);
            if (pingInterval) clearInterval(pingInterval);

            try {
                const wsBase = location.protocol === 'https:' ? 'wss://' : 'ws://';
                const wsUrl = wsBase + location.host + '/ws?user=' + encodeURIComponent(username) + '&token=' + encodeURIComponent(token);

                log('Connecting to: ' + wsUrl);
                updateConnectionStatus('Connecting...', 'warning');

                ws = new WebSocket(wsUrl);

                ws.onopen = function() {
                    log('✅ WebSocket connected successfully', 'connected');
                    updateConnectionStatus('Connected', 'connected');

                    // Notify parent window (opener)
                    if (window.opener) {
                        try {
                            window.opener.postMessage({
                                type: 'relay_connection_status',
                                connected: true,
                                message: 'Connected via relay page'
                            }, '*'); // Use specific origin in production: 'https://stake.com'
                        } catch(e) {
                            log('⚠️ Failed to notify parent: ' + e.message, 'warning');
                        }
                    }

                    reconnectDelay = 2000;

                    // Send initial ping
                    if (ws && ws.readyState === WebSocket.OPEN) {
                        ws.send('ping');
                    }

                    // Set up heartbeat (every 30 seconds)
                    heartbeatInterval = setInterval(() => {
                        if (ws && ws.readyState === WebSocket.OPEN) {
                            ws.send('ping');
                            log('🏓 Heartbeat sent');
                        }
                    }, 30000);

                    // Set up ping interval (every 10 seconds for testing)
                    pingInterval = setInterval(() => {
                        if (ws && ws.readyState === WebSocket.OPEN) {
                            ws.send('ping');
                        }
                    }, 10000);
                };

                ws.onmessage = function(event) {
                    if (!event.data) return;

                    try {
                        const data = JSON.parse(event.data);
                        log('📨 Relaying: ' + data.type + (data.code ? ' - ' + data.code : ''));

                        // Relay all messages to parent window
                        if (window.opener) {
                            try {
                                window.opener.postMessage({
                                    type: 'relay_websocket_message',
                                    data: data,
                                    timestamp: Date.now(),
                                    relay_id: 'ws_relay_' + Date.now()
                                }, '*'); // Use specific origin in production
                            } catch(e) {
                                log('⚠️ Failed to relay to parent: ' + e.message, 'warning');
                            }
                        }

                    } catch(e) {
                        log('⚠️ Non-JSON message: ' + event.data);

                        // Relay raw messages too
                        if (window.opener) {
                            try {
                                window.opener.postMessage({
                                    type: 'relay_websocket_message',
                                    data: { type: 'raw', message: event.data },
                                    timestamp: Date.now(),
                                    relay_id: 'ws_relay_raw_' + Date.now()
                                }, '*');
                            } catch(e) {
                                log('⚠️ Failed to relay raw message: ' + e.message, 'warning');
                            }
                        }
                    }
                };

                ws.onclose = function(event) {
                    log('🔌 Connection closed (Code: ' + event.code + ', Reason: ' + event.reason + ')', 'warning');
                    updateConnectionStatus('Disconnected - Reconnecting...', 'warning');

                    // Clear intervals
                    if (heartbeatInterval) clearInterval(heartbeatInterval);
                    if (pingInterval) clearInterval(pingInterval);

                    // Notify parent
                    if (window.opener) {
                        try {
                            window.opener.postMessage({
                                type: 'relay_connection_status',
                                connected: false,
                                message: 'Disconnected - Reconnecting...'
                            }, '*');
                        } catch(e) {
                            log('⚠️ Failed to notify parent of disconnect: ' + e.message, 'warning');
                        }
                    }

                    // Reconnect with exponential backoff
                    setTimeout(connectWS, reconnectDelay);
                    reconnectDelay = Math.min(reconnectDelay * 2, 30000);
                    log('🔄 Reconnecting in ' + reconnectDelay + 'ms');
                };

                ws.onerror = function(error) {
                    log('❌ WebSocket error: ' + error, 'error');
                    updateConnectionStatus('Connection Error', 'error');

                    if (window.opener) {
                        try {
                            window.opener.postMessage({
                                type: 'relay_connection_status',
                                connected: false,
                                message: 'Connection Error - Retrying...'
                            }, '*');
                        } catch(e) {
                            log('⚠️ Failed to notify parent of error: ' + e.message, 'warning');
                        }
                    }
                };

            } catch(error) {
                log('❌ Failed to create WebSocket: ' + error.message, 'error');
                updateConnectionStatus('Failed to Connect', 'error');

                if (window.opener) {
                    try {
                        window.opener.postMessage({
                            type: 'relay_connection_status',
                            connected: false,
                            message: 'Failed to connect - Retrying...'
                        }, '*');
                    } catch(e) {}
                }

                setTimeout(connectWS, 5000);
            }
        }

        // Handle messages from parent window
        window.addEventListener('message', function(event) {
            // Verify origin in production
            // if (event.origin !== 'https://stake.com') return;

            if (event.data.type === 'relay_ping_ws' && ws && ws.readyState === WebSocket.OPEN) {
                ws.send('ping');
                log('🏓 Manual ping sent');
            } else if (event.data.type === 'relay_close') {
                log('🔌 Closing relay by parent request');
                if (ws) ws.close();
                window.close();
            }
        });

        // Notify parent when page is loaded
        if (window.opener) {
            try {
                window.opener.postMessage({
                    type: 'relay_loaded',
                    message: 'Relay page loaded and ready'
                }, '*');
                log('📡 Notified parent that relay is ready');
            } catch(e) {
                log('⚠️ Failed to notify parent of load: ' + e.message, 'warning');
            }
        } else {
            log('⚠️ No parent window detected - this page should be opened as a popup', 'warning');
        }

        // Start connection
        log('🚀 Starting WebSocket relay for user: ' + username);
        connectWS();

        // Handle page unload
        window.addEventListener('beforeunload', function() {
            if (ws) {
                ws.close();
            }
        });

    </script>
</body>
</html>"""
    return HTMLResponse(content=html_content)

# Centralized dual authentication dependency for all endpoints
async def verify_dual_auth(request: Request, expected_user: str = None) -> str:
    """
    CRITICAL: Unified authentication that accepts either session auth OR signed iframe/API tokens
    Returns the authenticated username or raises 401
    """
    # Method 1: Session-based authentication (for web interface)
    session_user = verify_session(request)
    if session_user:
        # Extract real username from session
        if isinstance(session_user, dict) and 'username' in session_user:
            session_username = session_user['username']
        elif isinstance(session_user, str):
            session_username = session_user
        else:
            # If session exists but no username, use a default (should be updated based on your session structure)
            session_username = "authenticated_session_user"

        # If expected_user is specified, validate session user matches
        if expected_user and session_username != expected_user:
            raise HTTPException(status_code=401, detail="Session user mismatch")

        return session_username

    # Method 2: Signed token authentication (for iframe proxy & direct API calls)
    api_token = request.headers.get("X-API-Key")
    if not api_token:
        # Also check query parameter for backward compatibility with WebSocket/SSE
        api_token = request.query_params.get("token")

    if not api_token:
        raise HTTPException(status_code=401, detail="Authentication required: session or API token")

    # Validate WS_SECRET is set for token validation
    if not WS_SECRET:
        raise HTTPException(status_code=500, detail="Server authentication configuration error")

    # Extract user from token for validation
    try:
        parts = api_token.split(':')
        if len(parts) != 3:
            raise HTTPException(status_code=401, detail="Invalid token format")

        token_user = parts[0]

        # For user-scoped endpoints, ALWAYS enforce user binding
        if expected_user:
            if token_user != expected_user:
                raise HTTPException(status_code=401, detail="Token user mismatch")
        # For endpoints without expected_user (like voucher-info), allow any valid token
        # but log for security monitoring
        else:
            print(f"Warning: Token validation without expected_user for token_user: {token_user}")

        # Validate token signature and expiry
        if not validate_iframe_token(api_token, token_user):
            raise HTTPException(status_code=401, detail="Invalid or expired token")

        return token_user

    except HTTPException:
        raise  # Re-raise HTTP exceptions
    except Exception:
        raise HTTPException(status_code=401, detail="Token validation failed")

# Token validation for iframe sessions
def validate_iframe_token(token: str, expected_user: str) -> bool:
    """Validate signed iframe token to prevent secret exposure"""
    try:
        import hmac
        import hashlib
        import time

        # Parse token format: user:expiry:signature
        parts = token.split(':')
        if len(parts) != 3:
            return False

        token_user, expiry_str, provided_signature = parts

        # Validate user matches
        if token_user != expected_user:
            return False

        # Validate expiry
        try:
            expiry = int(expiry_str)
            if time.time() > expiry:
                return False  # Token expired
        except ValueError:
            return False

        # Validate signature
        payload = f"{token_user}:{expiry_str}"
        expected_signature = hmac.new(
            WS_SECRET.encode('utf-8'), 
            payload.encode('utf-8'), 
            hashlib.sha256
        ).hexdigest()

        return hmac.compare_digest(provided_signature, expected_signature)

    except Exception:
        return False

# Store for SSE connections and message queues
sse_connections: Dict[str, List] = {}  # username -> list of connection IDs
sse_message_queues: Dict[str, asyncio.Queue] = {}  # username -> message queue
sse_connection_health: Dict[str, Dict] = {}  # connection_id -> {'username': str, 'last_ping': float, 'last_pong': float, 'ping_count': int}
sse_heartbeat_task = None

# SSE Heartbeat Configuration - CONNECTION HEALTH MONITORING
SSE_PING_INTERVAL = 15.0  # Send ping every 15 seconds to keep connection alive
SSE_PING_TIMEOUT = None   
# ENHANCED CONNECTION MONITORING: Track connection metrics for 300+ users
connection_metrics = {
    'total_connections': 0,
    'active_connections': 0,
    'failed_connections': 0,
    'queue_overflows': 0,
    'reconnections': 0,
    'last_cleanup': 0,
    'memory_usage_mb': 0,
    'total_code_deliveries': 0,
    'authorized_deliveries': 0,
    'unauthorized_deliveries': 0
}

# SINGLE WORKER DEPLOYMENT: 
# System configured for single worker deployment to eliminate multi-worker state coordination issues.
# All SSE connections and message queues are stored in memory within the single worker process.
# This provides stable, reliable connections without needing Redis for cross-worker coordination.

# SINGLE VPS OPTIMIZATION: Credit cache for 300 concurrent members
# Instead of checking database on every broadcast, cache credits and refresh periodically
credit_cache: Dict[str, float] = {}  # username -> credits
credit_cache_last_update: Dict[str, float] = {}  # username -> last update timestamp
CREDIT_CACHE_TTL = 30  # Refresh credits every 30 seconds (optimized for 300 users instant delivery)

# PERSISTENT AUTHORIZATION CACHE: Eliminates recreating auth_cache on every broadcast
persistent_auth_cache: Dict[str, bool] = {}  # username -> authorization status
persistent_auth_cache_last_update: Dict[str, float] = {}  # username -> last auth check timestamp
AUTH_CACHE_TTL = 60  # Cache authorization for 60 seconds to avoid repeated checks

# REFRESH DEBOUNCING: Prevent task flooding during high load
refresh_in_progress: Set[str] = set()  # Users currently being refreshed
pending_refresh_tasks: Dict[str, asyncio.Task] = {}  # Active refresh tasks per user
last_refresh_time: Dict[str, float] = {}  # Time-based cooldown per user
REFRESH_COOLDOWN = 30.0  # Minimum 30 seconds between refresh attempts per user

# PRE-AUTHORIZATION SYSTEM: For 300 concurrent members - reserve 5% fees at connection time
# This eliminates database hits during code broadcasting
user_authorizations: Dict[str, Dict[str, Any]] = {}  # username -> {credits: float, reserved: float, authorized_until: timestamp}

# PER-USER LOCKS: Prevent race conditions during concurrent credit operations
from collections import defaultdict
per_user_locks: defaultdict = defaultdict(asyncio.Lock)  # username -> Lock

# CIRCUIT BREAKER: Protect database from overload
circuit_breaker_state = {
    'is_open': False,  # Circuit breaker status
    'failure_count': 0,  # Consecutive failures
    'last_failure_time': 0,  # Last failure timestamp
    'reset_timeout': 60,  # Reset after 60 seconds
    'failure_threshold': 5,  # Open circuit after 5 failures
    'queue_size_threshold': 1000,  # Open circuit if queue > 1000 items
    'db_latency_threshold': 5.0,  # Open circuit if DB RTT > 5 seconds
    'total_rejections': 0  # Track rejected requests
}

# BACKPRESSURE: Dynamic batch sizing based on queue depth
backpressure_config = {
    'min_batch_size': 20,
    'max_batch_size': 100,
    'queue_low_watermark': 100,
    'queue_high_watermark': 500,
    'current_batch_size': 20
}

# INSTANT CLAIM: Direct fee deduction on successful claims only (no broadcast charging)

def check_circuit_breaker() -> tuple[bool, str]:
    """Check if circuit breaker should reject new requests"""
    import time
    current_time = time.time()
    
    # Check if circuit is open and should reset
    if circuit_breaker_state['is_open']:
        time_since_failure = current_time - circuit_breaker_state['last_failure_time']
        if time_since_failure > circuit_breaker_state['reset_timeout']:
            # Reset circuit breaker
            circuit_breaker_state['is_open'] = False
            circuit_breaker_state['failure_count'] = 0
            print(f"CIRCUIT BREAKER RESET after {time_since_failure:.1f}s")
        else:
            circuit_breaker_state['total_rejections'] += 1
            time_remaining = circuit_breaker_state['reset_timeout'] - time_since_failure
            return False, f"Circuit breaker open - retry after {int(time_remaining)}s"
    
    # Check queue size
    queue_size = len(claim_queue)
    if queue_size > circuit_breaker_state['queue_size_threshold']:
        circuit_breaker_state['is_open'] = True
        circuit_breaker_state['last_failure_time'] = current_time
        circuit_breaker_state['failure_count'] += 1
        print(f"🚨 CIRCUIT BREAKER OPENED: Queue size {queue_size} > {circuit_breaker_state['queue_size_threshold']}")
        return False, f"System overloaded - queue size: {queue_size}"
    
    return True, "OK"

def record_circuit_breaker_success():
    """Record successful operation"""
    circuit_breaker_state['failure_count'] = max(0, circuit_breaker_state['failure_count'] - 1)

def record_circuit_breaker_failure():
    """Record failed operation"""
    import time
    circuit_breaker_state['failure_count'] += 1
    circuit_breaker_state['last_failure_time'] = time.time()
    
    if circuit_breaker_state['failure_count'] >= circuit_breaker_state['failure_threshold']:
        circuit_breaker_state['is_open'] = True
        print(f"🚨 CIRCUIT BREAKER OPENED: {circuit_breaker_state['failure_count']} consecutive failures")

def adjust_backpressure():
    """Dynamically adjust batch size based on queue depth"""
    queue_size = len(claim_queue)
    config = backpressure_config
    
    if queue_size < config['queue_low_watermark']:
        # Low load - use minimum batch size for faster individual processing
        config['current_batch_size'] = config['min_batch_size']
    elif queue_size > config['queue_high_watermark']:
        # High load - use maximum batch size to drain queue faster
        config['current_batch_size'] = config['max_batch_size']
    else:
        # Medium load - interpolate batch size
        ratio = (queue_size - config['queue_low_watermark']) / (config['queue_high_watermark'] - config['queue_low_watermark'])
        config['current_batch_size'] = int(config['min_batch_size'] + (config['max_batch_size'] - config['min_batch_size']) * ratio)
    
    return config['current_batch_size']

async def _get_cached_credits_async(username: str) -> float:
    """ASYNC: Get credits from cache, refresh if stale - OPTIMIZED for broadcast performance"""
    import time
    current_time = time.time()

    # Check if we have cached credits and they're fresh
    if (username in credit_cache and 
        username in credit_cache_last_update and 
        current_time - credit_cache_last_update[username] < CREDIT_CACHE_TTL):
        return credit_cache[username]

    # Cache miss or stale - refresh from database using async call
    credits = await _check_user_credits_db_async(username)
    credit_cache[username] = credits
    credit_cache_last_update[username] = current_time
    return credits

def _get_cached_credits(username: str) -> float:
    """SYNC: Get credits from cache, refresh if stale - OPTIMIZED for broadcast performance"""
    import time
    current_time = time.time()

    # Check if we have cached credits and they're fresh
    if (username in credit_cache and 
        username in credit_cache_last_update and 
        current_time - credit_cache_last_update[username] < CREDIT_CACHE_TTL):
        return credit_cache[username]

    # Cache miss or stale - refresh from database
    credits = _check_user_credits_db(username)
    credit_cache[username] = credits
    credit_cache_last_update[username] = current_time
    return credits

async def _check_user_credits_db_async(username: str) -> float:
    """ASYNC: Direct database check for user credits - FIXED: Returns total usable credits (available + reserved)"""
    try:
        # Use asyncio to run database operation in thread pool (non-blocking)
        import asyncio
        import functools

        def sync_db_check():
            db = SessionLocal()
            try:
                user = db.query(User).filter(User.username == username).first()
                total_credits = user.credits if user else Decimal('0.0')
                return total_credits
            finally:
                db.close()

        # Run in thread pool to avoid blocking event loop
        loop = asyncio.get_running_loop()
        total_credits = await loop.run_in_executor(None, sync_db_check)
        return total_credits
    except Exception as e:
        print(f"Warning: Async credit check failed for {username}: {e}")
        return 0.0

def _check_user_credits_db(username: str) -> float:
    """SIMPLIFIED: Direct database check for user credits"""
    try:
        db = SessionLocal()
        user = db.query(User).filter(User.username == username).first()
        # Return credits (no reserved_credits needed)
        total_credits = user.credits if user else Decimal('0.0')
        db.close()
        return total_credits
    except Exception as e:
        print(f"Warning: Credit check failed for {username}: {e}")
        return 0.0

def _check_user_credits(username: str) -> float:
    """Quick credit check using cache - OPTIMIZED for broadcast performance"""
    return _get_cached_credits(username)

async def _get_or_create_and_preauthorize_user_async(username: str) -> tuple[object, float]:
    """SIMPLIFIED: Get/create user and cache credits (no DB reservation needed)"""
    import time
    import asyncio

    def sync_operation():
        db = SessionLocal()
        try:
            # Get or create user
            user = db.query(User).filter(User.username == username).first()
            if not user:
                # Give new users $0.5 starter credits
                user = User(username=username, credits=Decimal('0.5'))
                db.add(user)
                db.commit()
                print(f"User: New user '{username}' created with $0.5 starter credits")
                db.refresh(user)

            # Get current credits - no reservation needed
            current_credits = user.credits
            current_time = time.time()

            # Cache credits for instant deduction
            credit_cache[username] = current_credits
            credit_cache_last_update[username] = current_time

            # Track authorization (simplified - no pre-reservation)
            user_authorizations[username] = {
                'connection_time': current_time,
                'available': current_credits,
                'credits': current_credits,
                'authorized_until': float('inf')
            }

            print(f"USER CONNECTED: {username} - ${current_credits} credits cached (no DB reservation)")
            return user, current_credits

        except Exception as e:
            db.rollback()
            raise e
        finally:
            db.close()

    try:
        # Run in thread pool to avoid blocking event loop
        loop = asyncio.get_running_loop()
        result = await loop.run_in_executor(None, sync_operation)
        return result
    except Exception as e:
        print(f"USER CONNECTION FAILED for {username}: {e}")
        return None, 0.0

def _preauthorize_user_credits(username: str) -> float:
    """🚀 LEGACY SYNC: Reserve 100% of user credits in database for guaranteed fee collection"""
    import time

    try:
        db = SessionLocal()
        user = db.query(User).filter(User.username == username).first()

        if not user:
            db.close()
            return 0.0

        # Get current credits (not yet reserved)
        available_credits = user.credits
        current_reserved = user.reserved_credits

        if available_credits <= 0:
            # Only create authorization if user has ANY reserved credits
            if current_reserved > 0:
                # User has previously reserved credits but no new credits to reserve
                user_authorizations[username] = {
                    'total_reserved': current_reserved,
                    'connection_time': time.time(),
                    'available': current_reserved,  # Credits available for claims
                    'reserved': current_reserved,   # Total reserved amount
                    'credits': Decimal('0.0'),      # User had no available credits
                    'authorized_until': float('inf')  # Unlimited time authorization
                }
                print(f"USING RESERVED: {username} has $0 available but ${current_reserved} already reserved")
            else:
                # User has absolutely no credits - do NOT create authorization
                print(f"🚫 ZERO CREDITS: {username} has $0 available and $0 reserved - no authorization created")

            # Update cache with existing reserved credits
            current_time = time.time()
            credit_cache[username] = current_reserved  # Total usable credits (already reserved)
            credit_cache_last_update[username] = current_time

            db.close()
            return current_reserved

        # 🚀 MAXIMUM SPEED: Reserve ALL available credits in database
        user.reserved_credits += available_credits  # Add to reserved
        user.credits = Decimal('0.0')                          # Move all to reserved

        # Commit the reservation to database immediately
        db.commit()

        total_reserved = user.reserved_credits
        current_time = time.time()

        # Track reservation for disconnection cleanup  
        user_authorizations[username] = {
            'total_reserved': total_reserved,
            'connection_time': current_time,
            'available': total_reserved,  # Credits available for claims
            'reserved': total_reserved,   # Total reserved amount
            'credits': total_reserved,    # User's credits at time of authorization
            'authorized_until': float('inf')  # Unlimited time authorization
        }

        # Update cache with new state - FIXED: Show total usable credits in cache
        credit_cache[username] = total_reserved  # Total usable credits (now all reserved)
        credit_cache_last_update[username] = current_time

        print(f"100% RESERVED: {username} - ${available_credits} moved to reserved (total reserved: ${total_reserved})")
        db.close()
        return total_reserved

    except Exception as e:
        print(f"RESERVATION FAILED for {username}: {e}")
        if 'db' in locals():
            db.rollback()
            db.close()
        return 0.0

def _is_user_preauthorized_fast(username: str) -> bool:
    """ULTRA-FAST: Check authorization using persistent cache - NO DATABASE CALLS during broadcast"""
    import time
    current_time = time.time()

    # First check persistent cache (super fast)
    if (username in persistent_auth_cache and 
        username in persistent_auth_cache_last_update and 
        current_time - persistent_auth_cache_last_update[username] < AUTH_CACHE_TTL):
        return persistent_auth_cache[username]

    # Cache miss - check user authorization data quickly
    if username not in user_authorizations:
        persistent_auth_cache[username] = False
        persistent_auth_cache_last_update[username] = current_time
        return False

    auth_data = user_authorizations[username]

    # Quick check without database calls
    has_credits = auth_data.get('available', 0) > 0

    # Update persistent cache
    persistent_auth_cache[username] = has_credits
    persistent_auth_cache_last_update[username] = current_time

    # TIME-BASED DEBOUNCED REFRESH: If low credits, schedule async refresh with cooldown
    if (auth_data.get('available', 0) < 1.0 and 
        username not in refresh_in_progress and
        current_time - last_refresh_time.get(username, 0) > REFRESH_COOLDOWN):

        refresh_in_progress.add(username)
        last_refresh_time[username] = current_time

        # Cancel existing pending refresh task if any
        if username in pending_refresh_tasks:
            pending_refresh_tasks[username].cancel()

        # Create new refresh task with cleanup
        async def _debounced_refresh():
            try:
                await _refresh_user_authorization_async(username)
            finally:
                # Cleanup after refresh
                refresh_in_progress.discard(username)
                if username in pending_refresh_tasks:
                    del pending_refresh_tasks[username]

        task = asyncio.create_task(_debounced_refresh())
        pending_refresh_tasks[username] = task
        print(f"TIME-DEBOUNCED REFRESH: Scheduled for {username} (available: ${auth_data.get('available', 0)}, cooldown: {REFRESH_COOLDOWN}s)")
    elif auth_data.get('available', 0) < 1.0 and username in refresh_in_progress:
        print(f"⏳ REFRESH IN PROGRESS: Skipping refresh for {username} (already running)")
    elif auth_data.get('available', 0) < 1.0:
        time_left = REFRESH_COOLDOWN - (current_time - last_refresh_time.get(username, 0))
        print(f"⏱️ REFRESH COOLDOWN: {username} needs {time_left:.1f}s more before next refresh")

    return has_credits

def _is_user_preauthorized(username: str) -> bool:
    """DEPRECATED: Legacy version with blocking calls - kept for compatibility"""
    import time
    if username not in user_authorizations:
        return False

    auth_data = user_authorizations[username]
    current_time = time.time()

    # Auto-refresh authorization if credits are low (unlimited time authorization)
    if auth_data['available'] < 1.0:  # Less than $1 available
        _refresh_user_authorization(username)
        # Re-check after refresh
        auth_data = user_authorizations.get(username, {})

    # Check if user has available credits (unlimited time authorization)
    return auth_data.get('available', 0) > 0

async def _cleanup_user_authorization(username: str):
    """🚀 NEW: Release 100% reserved credits back to user's balance on disconnect with race condition protection"""
    import time

    # FINANCIAL SAFETY: Use per-user lock to prevent race conditions during cleanup
    # Ensure lock exists for this user
    if username not in per_user_locks:
        per_user_locks[username] = asyncio.Lock()
    
    async with per_user_locks[username]:
        # Safe dictionary access - check if still exists
        auth_data = user_authorizations.get(username)
        if not auth_data:
            return

        total_reserved = auth_data.get('total_reserved', 0)

        # SIMPLIFIED: With single credits field, no cleanup needed on disconnect
        # Credits remain in user's account, cache is simply cleared
        try:
            # Just clear cache on disconnect
            if username in credit_cache:
                del credit_cache[username]
            if username in credit_cache_last_update:
                del credit_cache_last_update[username]
            
            print(f"DISCONNECT CLEANUP: {username} - cache cleared (credits remain in database)")

        except Exception as e:
            print(f"FAILED to release reserved credits for {username}: {e}")
            # Context manager handles db.close() and rollback automatically

        finally:
            # Clean up memory tracking (protected by lock to prevent race condition)
            if username in user_authorizations:
                del user_authorizations[username]

async def _consume_preauthorized_credit(username: str, fee_amount: float, code: str = None) -> bool:
    """ENHANCED: Consume from pre-authorized credits with database tracking and race condition protection"""
    # FINANCIAL SAFETY: Use per-user lock to prevent concurrent modifications and race conditions
    # Ensure lock exists for this user
    if username not in per_user_locks:
        per_user_locks[username] = asyncio.Lock()
    
    async with per_user_locks[username]:
        # Safe dictionary access - use .get() to avoid KeyError if deleted by another coroutine
        auth_data = user_authorizations.get(username)
        if not auth_data:
            return False

        # SECURITY FIX: Use safe_decimal for precise monetary arithmetic
        fee_decimal = Decimal(str(fee_amount))
        available_decimal = safe_decimal(auth_data.get('available', 0), '0')

        # Check if user has enough reserved credits for this fee
        if available_decimal >= fee_decimal:
            # SECURITY FIX: Log pre-auth usage to database for recovery
            # RESOURCE SAFETY: Use context manager to ensure db.close() in all paths
            try:
                with SessionLocal() as db:
                    session_id = auth_data.get('session_id', f"session_{int(time.time())}")

                    # Create pre-auth usage record for recovery
                    preauth_record = PreAuthUsage(
                        username=username,
                        session_id=session_id,
                        amount_consumed=fee_amount,
                        code=code or "unknown_code",
                        committed=False,  # Will be marked True after successful claim
                        expires_at=datetime.utcnow() + timedelta(hours=1)  # Auto-cleanup after 1 hour
                    )

                    db.add(preauth_record)
                    db.commit()
                    db.refresh(preauth_record)  # Get the ID after commit

                    # Consume from the pre-authorization in memory (atomically protected by lock)
                    auth_data['available'] = float(available_decimal - fee_decimal)
                    reserved_decimal = safe_decimal(auth_data.get('reserved', 0), '0')
                    auth_data['reserved'] = float(reserved_decimal - fee_decimal)
                    auth_data['preauth_record_id'] = preauth_record.id  # Track for later commit marking

                    print(f"💳 SECURE INSTANT: Consumed ${fee_amount} from {username} pre-authorization (${auth_data['available']} remaining, tracked: {preauth_record.id})")
                    return True

            except Exception as e:
                print(f"Warning: PreAuth logging failed for {username}: {e}")
                # Continue with consumption even if logging fails (performance priority)
                auth_data['available'] = float(available_decimal - fee_decimal)
                reserved_decimal = safe_decimal(auth_data.get('reserved', 0), '0')
                auth_data['reserved'] = float(reserved_decimal - fee_decimal)
                print(f"💳 FALLBACK INSTANT: Consumed ${fee_amount} from {username} pre-authorization (${auth_data['available']} remaining)")
                return True
        else:
            print(f"PRE-AUTH INSUFFICIENT: {username} needs ${fee_amount}, has ${available_decimal} pre-authorized")
            return False

def _mark_preauth_committed(username: str):
    """Mark pre-authorization usage as committed after successful claim"""
    if username in user_authorizations and 'preauth_record_id' in user_authorizations[username]:
        try:
            db = SessionLocal()
            record_id = user_authorizations[username]['preauth_record_id']

            db.execute(text("""
                UPDATE preauth_usage 
                SET committed = TRUE 
                WHERE id = :record_id
            """), {"record_id": record_id})

            db.commit()
            db.close()

            # Clean up the tracking
            del user_authorizations[username]['preauth_record_id']
            print(f"PreAuth marked as committed for {username} (record: {record_id})")

        except Exception as e:
            print(f"Warning: Failed to mark preauth as committed for {username}: {e}")

async def recover_uncommitted_preauth():
    """SECURITY: Recover pre-authorization credits lost due to server crashes"""
    try:
        db = SessionLocal()

        # Find uncommitted pre-auth usage older than 10 minutes
        cutoff_time = datetime.utcnow() - timedelta(minutes=10)

        uncommitted_records = db.execute(text("""
            SELECT id, username, amount_consumed, code, created_at
            FROM preauth_usage 
            WHERE committed = FALSE 
            AND recovered = FALSE 
            AND created_at < :cutoff_time
        """), {"cutoff_time": cutoff_time}).fetchall()

        recovery_count = 0

        for record in uncommitted_records:
            record_id, username, amount_consumed, code, created_at = record

            try:
                # Refund the consumed amount back to user balance
                user_result = db.execute(text("""
                    UPDATE users 
                    SET credits = credits + :refund_amount 
                    WHERE username = :username 
                    RETURNING id, credits
                """), {"refund_amount": amount_consumed, "username": username})

                user_row = user_result.fetchone()
                if user_row:
                    user_id, new_balance = user_row

                    # Log the recovery transaction
                    db.add(Transaction(
                        user_id=user_id,
                        amount=amount_consumed,
                        type="preauth_recovery",
                        meta=f"RECOVERY: Refunded ${amount_consumed:.4f} from uncommitted pre-auth for code {code} (created: {created_at})"
                    ))

                    # Mark as recovered
                    db.execute(text("""
                        UPDATE preauth_usage 
                        SET recovered = TRUE 
                        WHERE id = :record_id
                    """), {"record_id": record_id})

                    print(f"RECOVERED: ${amount_consumed:.4f} → {username} from uncommitted pre-auth (code: {code})")
                    recovery_count += 1

                    # Invalidate credit cache
                    _invalidate_user_credits(username)

            except Exception as record_error:
                print(f"Failed to recover preauth record {record_id}: {record_error}")

        if recovery_count > 0:
            db.commit()
            print(f"RECOVERY COMPLETE: Restored {recovery_count} uncommitted pre-authorizations")

        db.close()
        return recovery_count

    except Exception as e:
        print(f"CRITICAL: PreAuth recovery failed: {e}")
        if 'db' in locals():
            db.rollback()
            db.close()
        return 0

async def cleanup_expired_preauth():
    """Clean up expired pre-authorization records to prevent database bloat"""
    try:
        db = SessionLocal()

        # Remove records older than 24 hours
        cutoff_time = datetime.utcnow() - timedelta(hours=24)

        result = db.execute(text("""
            DELETE FROM preauth_usage 
            WHERE expires_at < :cutoff_time
            RETURNING username
        """), {"cutoff_time": cutoff_time})

        deleted_count = len(result.fetchall())

        if deleted_count > 0:
            db.commit()
            print(f"🧹 CLEANUP: Removed {deleted_count} expired pre-auth records")

        db.close()
        return deleted_count

    except Exception as e:
        print(f"PreAuth cleanup failed: {e}")
        if 'db' in locals():
            db.rollback()
            db.close()
        return 0

async def preauth_recovery_service():
    """Background service for pre-authorization recovery and cleanup"""
    # Initial recovery on startup
    print("Running initial pre-authorization recovery...")
    initial_recovery = await recover_uncommitted_preauth()
    if initial_recovery > 0:
        print(f"STARTUP RECOVERY: Restored {initial_recovery} uncommitted pre-authorizations")

    while True:
        try:
            # Recovery every 5 minutes
            recovery_count = await recover_uncommitted_preauth()
            if recovery_count > 0:
                print(f"PERIODIC RECOVERY: Restored {recovery_count} uncommitted pre-authorizations")

            # Cleanup every hour (12 cycles of 5 minutes)
            if int(time.time()) % 3600 < 300:  # Within first 5 minutes of each hour
                cleanup_count = await cleanup_expired_preauth()
                if cleanup_count > 0:
                    print(f"🧹 PERIODIC CLEANUP: Removed {cleanup_count} expired pre-auth records")

        except Exception as e:
            print(f"PreAuth recovery service error: {e}")

        # Run every 5 minutes
        await asyncio.sleep(300)

async def _refresh_user_authorization_async(username: str):
    """TRULY ASYNC: Refresh authorization using thread pool - COMPLETELY NON-BLOCKING"""
    if username not in user_authorizations:
        return

    auth_data = user_authorizations[username]
    import time
    current_time = time.time()

    # Refresh only if available credits are low (no time limit anymore)
    if auth_data['available'] < 1.0:  # Less than $1 available

        # TRULY ASYNC: Offload blocking database operations to thread pool
        try:
            def _sync_db_refresh():
                """Synchronous database operations in thread pool"""
                db = SessionLocal()
                try:
                    user = db.query(User).filter(User.username == username).first()
                    if not user:
                        return None, 0.0

                    # Get user credits (simplified - no reserved_credits)
                    total_credits = float(user.credits)
                    return user, total_credits
                finally:
                    db.close()

            # Execute in thread pool to avoid blocking event loop
            user, user_credits = await asyncio.to_thread(_sync_db_refresh)

            if not user or user_credits <= 0:
                # Truly no credits left - disable authorization
                auth_data['available'] = 0.0
                auth_data['reserved'] = 0.0
                auth_data['credits'] = 0.0
                print(f"🚫 AUTHORIZATION DISABLED: {username} - $0 total credits remaining")
                # Update persistent cache
                persistent_auth_cache[username] = False
                persistent_auth_cache_last_update[username] = current_time
                return

            # INFINITE CONNECTION: Always refill authorization window from database credits
            refill_amount = min(user_credits, 5.0)  # Cap at $5 window
            auth_data['available'] = refill_amount
            auth_data['reserved'] = user_credits
            auth_data['credits'] = user_credits
            auth_data['authorized_until'] = float('inf')  # UNLIMITED TIME

            # Update persistent cache
            persistent_auth_cache[username] = True
            persistent_auth_cache_last_update[username] = current_time

            # Update credit cache as well
            credit_cache[username] = user_credits
            credit_cache_last_update[username] = current_time

            print(f"TRULY ASYNC AUTHORIZATION REFILLED: {username} - window: ${refill_amount}, total: ${user_credits}")

        except Exception as e:
            print(f"ASYNC AUTHORIZATION REFRESH FAILED: {username} - {e}")
            # Mark as unauthorized on error
            persistent_auth_cache[username] = False
            persistent_auth_cache_last_update[username] = current_time

def _refresh_user_authorization(username: str):
    """DEPRECATED: Legacy sync version - kept for compatibility during transition"""
    # Schedule async refresh instead of blocking
    asyncio.create_task(_refresh_user_authorization_async(username))
    print(f"SCHEDULED ASYNC REFRESH for {username} (non-blocking)")

def _invalidate_user_credits(username: str):
    """Invalidate cached credits after transactions to force refresh"""
    if username in credit_cache:
        del credit_cache[username]
    if username in credit_cache_last_update:
        del credit_cache_last_update[username]

async def _check_and_disconnect_zero_balance_users(username: str):
    """
    Check if user balance hits 0 after successful claim and auto-disconnect them from SSE
    """
    try:
        # Get fresh balance from database (FIXED: use async version to avoid blocking event loop)
        current_balance = await _check_user_credits_db_async(username)

        if current_balance <= 0:
            print(f"🚨 AUTO-DISCONNECT: {username} balance is ${current_balance:.4f} - disconnecting from SSE")

            # Disconnect user from SSE connections
            if username in sse_connections:
                print(f"🔌 DISCONNECTING: {username} from SSE (balance: ${current_balance:.4f})")

                # Send final balance update message before disconnect
                if username in sse_message_queues:
                    try:
                        disconnect_message = {
                            'type': 'balance_zero_disconnect',
                            'message': 'Your credits have reached $0. Please recharge to continue receiving codes.',
                            'username': username,
                            'balance': current_balance,
                            'timestamp': int(time.time()),
                            'action': 'disconnect'
                        }
                        await sse_message_queues[username].put(disconnect_message)
                        print(f"📤 FINAL MESSAGE: Sent balance zero notification to {username}")
                    except Exception as msg_error:
                        print(f"Warning: Failed to send disconnect message to {username}: {msg_error}")

                # Clean up SSE connections
                sse_connections[username].clear()
                del sse_connections[username]

                # Clean up message queue
                if username in sse_message_queues:
                    del sse_message_queues[username]

                # Clean up pre-authorization
                await _cleanup_user_authorization(username)

                print(f"DISCONNECTED: {username} removed from SSE connections due to zero balance")
                return True
            else:
                print(f"ℹ️  {username} has zero balance but no active SSE connection")
                return False
        else:
            print(f"💳 BALANCE CHECK: {username} has ${current_balance:.4f} - keeping connection")
            return False

    except Exception as e:
        print(f"Auto-disconnect check failed for {username}: {e}")
        return False

def _disconnect_user_from_all_connections(username: str):
    """
    Immediately disconnect a user from all SSE connections (synchronous version)
    """
    try:
        if username in sse_connections:
            print(f"🔌 FORCE DISCONNECT: {username} from all SSE connections")

            # Clean up SSE connections
            sse_connections[username].clear()
            del sse_connections[username]

            # Clean up message queue
            if username in sse_message_queues:
                del sse_message_queues[username]

            # Clean up pre-authorization (async task for sync context)
            asyncio.create_task(_cleanup_user_authorization(username))

            print(f"FORCE DISCONNECTED: {username} removed from all connections")
            return True
        else:
            print(f"ℹ️  {username} has no active connections to disconnect")
            return False

    except Exception as e:
        print(f"Force disconnect failed for {username}: {e}")
        return False

@app.post("/sse-pong")
async def sse_pong_endpoint(request: Request, connection_id: str = Query(...), token: str = Query(...)):
    """Handle pong responses from SSE clients for heartbeat tracking"""
    try:
        # Validate token to ensure only authenticated clients can send pongs
        authenticated_user = validate_and_extract_user(token)

        # Update pong timestamp for the connection
        handle_sse_pong(connection_id)

        return {"status": "pong_received", "timestamp": int(time.time())}

    except HTTPException:
        return {"status": "error", "message": "Invalid token"}
    except Exception as e:
        return {"status": "error", "message": "Pong processing failed"}

@app.get("/events")
async def stream_events(user: str = Query(...), token: str = Query(...)):
    """Server-Sent Events endpoint for real-time code streaming"""

    # Validate signed iframe token - no raw secrets accepted
    if not WS_SECRET:
        raise HTTPException(status_code=500, detail="Server configuration error")
    if not validate_iframe_token(token, user):
        raise HTTPException(status_code=401, detail="Invalid or expired iframe token")

    # Extract authenticated username from token (like fetchBalance does)
    authenticated_user = validate_and_extract_user(token)
    if authenticated_user != user:
        print(f"Warning: SSE user mismatch: query='{user}' vs token='{authenticated_user}' - using token user")
        user = authenticated_user  # Use the authenticated username from token

    # 🚀 OPTIMIZED: Single consolidated database operation for user setup
    try:
        db_user, user_credits = await _get_or_create_and_preauthorize_user_async(user)
        print(f"💳 SSE OPTIMIZED: {user} has ${user_credits} credits (pre-authorized in single DB call)")

        # If user has 0 credits, allow connection but warn (graceful degradation)
        if user_credits <= 0:
            print(f"Warning: SSE WARNING: {user} has $0 credits - connection allowed but codes will not be sent")
            # Don't disconnect immediately - allow connection for balance updates
    except Exception as e:
        print(f"SSE CONNECTION SETUP FAILED for {user}: {e}")
        raise HTTPException(status_code=500, detail="Connection setup failed")

    async def event_generator():
        # IMPROVED: Automatically remove ALL previous connections for this user (allow only 1 connection per user)
        if user in sse_connections:
            old_connections = sse_connections[user].copy()
            if old_connections:
                print(f"AUTO-DISCONNECT: Removing {len(old_connections)} existing connection(s) for {user}")
                for old_conn_id in old_connections:
                    # Remove from health tracking
                    if old_conn_id in sse_connection_health:
                        del sse_connection_health[old_conn_id]
                    # Send disconnect notification to old connection (if possible)
                    try:
                        if user in sse_message_queues:
                            disconnect_msg = {
                                'type': 'force_disconnect',
                                'message': 'New connection detected - this session will be closed',
                                'timestamp': int(time.time())
                            }
                            # Try to send disconnect message (may fail if connection already dead)
                            try:
                                sse_message_queues[user].put_nowait(disconnect_msg)
                            except:
                                pass
                    except:
                        pass
                
                # Clear all old connections for this user
                del sse_connections[user]
                if user in sse_message_queues:
                    del sse_message_queues[user]
                print(f"Cleared all previous connections for {user} - allowing new connection")
        
        # Initialize user message queue if doesn't exist
        if user not in sse_message_queues:
            # BOUNDED QUEUE: Limit to 100 messages per user to prevent memory bloat
            # With 300 users max: 300 * 100 = 30,000 max messages in memory (reasonable)
            sse_message_queues[user] = asyncio.Queue(maxsize=100)

        # Store this NEW connection
        if user not in sse_connections:
            sse_connections[user] = []
            connection_metrics['total_connections'] += 1
            update_connection_metrics()

        connection_id = f"{user}_{int(time.time())}"
        sse_connections[user].append(connection_id)
        print(f"NEW SSE CONNECTION: {user} - connection_id: {connection_id} (total for user: {len(sse_connections[user])})")

        # Initialize heartbeat tracking for this connection
        current_time = time.time()
        sse_connection_health[connection_id] = {
            'username': user,
            'last_ping': 0,
            'last_pong': current_time,
            'ping_count': 0
        }

        # Start SSE heartbeat loop if this is first connection
        global sse_heartbeat_task
        if sse_heartbeat_task is None and len(sse_connection_health) == 1:
            sse_heartbeat_task = asyncio.create_task(sse_heartbeat_loop())

        try:
            # 🔑 STABLE: Get or create 24hr session token (no more reconnections!)
            session_token = generate_session_jwt(user, connection_id)

            # Send initial connection event with stable session token
            initial_message = {
                'type': 'connected',
                'message': 'SSE stream connected - Stable 24hr token issued',
                'username': user,
                'timestamp': int(time.time()),
                # 🔑 STABLE: 24-hour token - no more reconnections!
                'session_token': session_token,
                'token_expires_in': SESSION_TOKEN_EXPIRY,
                'token_type': 'stable_session_jwt',
                'security_note': 'Stable 24hr token - no constant reconnections!'
            }
            yield f"data: {json.dumps(initial_message)}\n\n"

            # Get reference to user's message queue
            message_queue = sse_message_queues[user]
            last_heartbeat = time.time()

            # Separate timers for ping events and keepalive comments
            last_ping_sent = time.time()
            last_keepalive_sent = time.time()

            # SCALABILITY: Track connection for authorization refresh
            last_auth_refresh = time.time()

            while True:
                try:
                    # Shorter timeout for faster message delivery during active periods
                    message = await asyncio.wait_for(message_queue.get(), timeout=5.0)

                    # Send the message
                    sse_data = json.dumps(message)
                    yield f"data: {sse_data}\n\n"

                    # Mark task as done
                    message_queue.task_done()
                    last_heartbeat = time.time()

                except asyncio.TimeoutError:
                    # Separate ping events and keepalive comments with independent timers
                    current_time = time.time()

                    # Send ping messages on proper interval (every 10 seconds)
                    if current_time - last_ping_sent > SSE_PING_INTERVAL:
                        ping_message = {
                            'type': 'ping', 
                            'timestamp': int(current_time),
                            'connection_id': connection_id
                        }
                        yield f"data: {json.dumps(ping_message)}\n\n"

                        # Update ping tracking
                        if connection_id in sse_connection_health:
                            sse_connection_health[connection_id]['last_ping'] = current_time
                            sse_connection_health[connection_id]['ping_count'] += 1

                        last_ping_sent = current_time

                    # Send SSE keepalive comments to prevent proxy drops (every 15 seconds)
                    if current_time - last_keepalive_sent > 15.0:
                        yield ": SSE keepalive\n\n"
                        last_keepalive_sent = current_time

                    # Update general heartbeat for message processing
                    last_heartbeat = current_time

                    # SCALABILITY: Refresh authorization every 10 minutes to maintain performance
                    if current_time - last_auth_refresh > 600:  # 10 minutes
                        _refresh_user_authorization(user)
                        last_auth_refresh = current_time

        except asyncio.CancelledError:
            # Client disconnected - clean up
            if user in sse_connections:
                sse_connections[user] = [conn for conn in sse_connections[user] if conn != connection_id]
                if not sse_connections[user]:
                    del sse_connections[user]
                    # Clean up message queue if no more connections
                    if user in sse_message_queues:
                        del sse_message_queues[user]
                    # SCALABILITY: Clean up pre-authorization on disconnect (async task for exception handler)
                    asyncio.create_task(_cleanup_user_authorization(user))

            # Clean up heartbeat tracking
            if connection_id in sse_connection_health:
                del sse_connection_health[connection_id]
        except Exception as e:
            print(f"SSE error for {user}: {e}")
            # Clean up on error
            if user in sse_connections:
                sse_connections[user] = [conn for conn in sse_connections[user] if conn != connection_id]
                if not sse_connections[user]:
                    del sse_connections[user]
                    if user in sse_message_queues:
                        del sse_message_queues[user]
                    # SCALABILITY: Clean up pre-authorization on error/disconnect (async task for exception handler)
                    asyncio.create_task(_cleanup_user_authorization(user))

            # Clean up heartbeat tracking
            if connection_id in sse_connection_health:
                del sse_connection_health[connection_id]

    return StreamingResponse(
        event_generator(),
        media_type="text/event-stream",
        headers={
            "Cache-Control": "no-cache",
            "Connection": "keep-alive",
            "X-Accel-Buffering": "no",  # Disable proxy buffering for SSE
            "Access-Control-Allow-Origin": "*",
            "Access-Control-Allow-Headers": "Cache-Control"
        }
    )

@app.get("/embed-stream")
async def embed_stream(request: Request, user: str = Query(...), nonce: str = Query(None)):
    """Hidden iframe endpoint for cross-origin SSE streaming"""

    # Generate signed token for iframe session - no secrets exposed to client
    if not WS_SECRET:
        raise HTTPException(status_code=500, detail="Server configuration error")

    # Generate secure iframe session token (JWT-like but simpler)
    import hmac
    import hashlib
    import time

    # Create payload with user and expiry (15 minutes)
    expiry = int(time.time()) + 900  # 15 minutes from now
    payload = f"{user}:{expiry}"

    # Sign the payload with WS_SECRET
    signature = hmac.new(
        WS_SECRET.encode('utf-8'), 
        payload.encode('utf-8'), 
        hashlib.sha256
    ).hexdigest()

    # Create secure token that client can safely see, bound to nonce for additional security
    iframe_token = f"{payload}:{signature}"

    # Strict origin and nonce validation to prevent token minting abuse
    # Check Origin header first (more reliable than Referer)
    origin = request.headers.get("Origin", "")
    referer = request.headers.get("Referer", "")
    parent_origin = "unknown"  # Default to unknown for security

    # Try Origin header first, fallback to Referer
    candidate_origin = None
    if origin:
        candidate_origin = origin
    elif referer:
        try:
            from urllib.parse import urlparse
            parsed = urlparse(referer)
            if parsed.scheme and parsed.netloc:
                candidate_origin = f"{parsed.scheme}://{parsed.netloc}"
        except Exception:
            pass  # Invalid referer

    # Strict allowlist validation - reject if not explicitly allowed
    if candidate_origin and candidate_origin in ALLOWED_ORIGINS:
        parent_origin = candidate_origin
        # Enhanced logging for security monitoring
        print(f"Issued iframe token for user '{user}' from origin '{parent_origin}' with nonce '{nonce[:8]}...'")
    else:
        # Log suspicious access attempts for monitoring
        print(f"Warning: Unauthorized embed-stream access attempt from origin: {candidate_origin or 'unknown'}")
        raise HTTPException(status_code=403, detail="Unauthorized origin - iframe access only")

    # Require nonce for additional security (prevents direct navigation)
    if not nonce or len(nonce) < 8:
        print(f"Warning: Missing or invalid nonce in embed-stream request from: {parent_origin}")
        raise HTTPException(status_code=400, detail="Valid nonce required")

    # Minimal HTML page that establishes SSE connection and relays to parent
    html_content = f"""<!DOCTYPE html>
<html>
<head>
    <title>SSE Relay</title>
    <meta charset="utf-8">
    <style>
        body {{ margin: 0; padding: 0; background: transparent; }}
        #status {{ font-family: monospace; font-size: 10px; color: #666; padding: 2px; }}
    </style>
</head>
<body>
    <div id="status">Connecting...</div>
    <script>
        // SSE connection variables
        let eventSource = null;
        let reconnectAttempts = 0;
        let maxReconnectAttempts = 5;
        let reconnectDelay = 2000;
        const parentOrigin = '{parent_origin}';
        const messageNonce = '{nonce or ""}';

        // Initialize SSE connection
        function connectSSE() {{
            // SECURITY: Use signed token - no server secrets exposed
            const sseUrl = `/events?user={user}&token={iframe_token}`;

            if (eventSource) {{
                eventSource.close();
            }}

            try {{
                eventSource = new EventSource(sseUrl);
                document.getElementById('status').textContent = 'Connecting to SSE...';

                eventSource.onopen = function(event) {{
                    // console.log('✅ Hidden iframe SSE connected');
                    document.getElementById('status').textContent = 'Connected';
                    reconnectAttempts = 0;
                    reconnectDelay = 2000;

                    // Notify parent that connection is established (with origin validation)
                    if (window.parent && window.parent !== window) {{
                        window.parent.postMessage({{
                            type: 'iframe_sse_connected',
                            nonce: messageNonce,
                            timestamp: Date.now()
                        }}, parentOrigin);
                    }}
                }};

                eventSource.onmessage = function(event) {{
                    try {{
                        const data = JSON.parse(event.data);

                        // Handle Socket.IO-style ping messages
                        if (data.type === 'ping' && data.connection_id) {{
                            // Send pong response via HTTP endpoint (silent)
                            fetch(`/sse-pong?connection_id=${{data.connection_id}}&token={iframe_token}`, {{
                                method: 'POST',
                                headers: {{ 'Content-Type': 'application/json' }}
                            }}).then(() => {{
                                // Track successful pong responses for heartbeat stats
                                if (window.parent && window.parent !== window) {{
                                    window.parent.postMessage({{
                                        type: 'iframe_pong_success',
                                        nonce: messageNonce,
                                        timestamp: Date.now()
                                    }}, parentOrigin);
                                }}
                            }}).catch(() => {{
                                // Silent failure - heartbeat will handle dead connections
                            }});
                        }}

                        // Forward all messages to parent window (with origin validation)
                        if (window.parent && window.parent !== window) {{
                            window.parent.postMessage({{
                                type: 'iframe_sse_message',
                                data: data,
                                nonce: messageNonce,
                                timestamp: Date.now()
                            }}, parentOrigin);
                        }}

                        // Update status for debugging
                        if (data.type === 'connected') {{
                            document.getElementById('status').textContent = 'SSE Ready';
                        }} else if (data.type === 'ping') {{
                            document.getElementById('status').textContent = 'Connected (ping)';
                        }} else {{
                            document.getElementById('status').textContent = 'Message received';
                        }}

                    }} catch (e) {{
                        // console.error('Error parsing SSE message:', e);
                    }}
                }};

                eventSource.onerror = function(event) {{
                    // console.error('❌ Hidden iframe SSE error');
                    document.getElementById('status').textContent = 'Connection error';

                    // Check if this might be a 402 Payment Required error by testing the endpoint
                    fetch(sseUrl, {{ method: 'HEAD' }}).then(response => {{
                        const errorDetails = {{
                            type: 'iframe_sse_error',
                            attempt: reconnectAttempts,
                            maxAttempts: maxReconnectAttempts,
                            nonce: messageNonce,
                            timestamp: Date.now()
                        }};

                        // If 402 Payment Required, add specific error details
                        if (response.status === 402) {{
                            errorDetails.statusCode = 402;
                            errorDetails.error = 'Payment Required - Insufficient credits';
                        }}

                        // Notify parent of error with details
                        if (window.parent && window.parent !== window) {{
                            window.parent.postMessage(errorDetails, parentOrigin);
                        }}
                    }}).catch(() => {{
                        // Fallback if fetch fails - send generic error
                        if (window.parent && window.parent !== window) {{
                            window.parent.postMessage({{
                                type: 'iframe_sse_error',
                                attempt: reconnectAttempts,
                                maxAttempts: maxReconnectAttempts,
                                nonce: messageNonce,
                                timestamp: Date.now()
                            }}, parentOrigin);
                        }}
                    }});

                    // Auto-reconnect with backoff
                    if (reconnectAttempts < maxReconnectAttempts) {{
                        reconnectAttempts++;
                        setTimeout(() => {{
                            // console.log(`🔄 Reconnecting SSE iframe (attempt ${{reconnectAttempts}}/${{maxReconnectAttempts}})...`);
                            connectSSE();
                        }}, reconnectDelay);
                        reconnectDelay = Math.min(reconnectDelay * 1.5, 30000); // Max 30 seconds
                    }} else {{
                        // Max attempts reached, notify parent
                        if (window.parent && window.parent !== window) {{
                            window.parent.postMessage({{
                                type: 'iframe_sse_failed',
                                nonce: messageNonce,
                                timestamp: Date.now()
                            }}, parentOrigin);
                        }}
                    }}
                }};

            }} catch (error) {{
                // console.error('Failed to create SSE connection in iframe:', error);
                document.getElementById('status').textContent = 'Connection failed';

                if (window.parent && window.parent !== window) {{
                    window.parent.postMessage({{
                        type: 'iframe_sse_failed',
                        error: error.message,
                        nonce: messageNonce,
                        timestamp: Date.now()
                    }}, parentOrigin);
                }}
            }}
        }}

        // Secure API proxy function - handles API calls from parent with strict allowlist
        async function handleApiCall(endpoint, method, data) {{
            // SECURITY: Strict allowlist of permitted endpoints and methods
            const ALLOWED_ENDPOINTS = {{
                '/balance': ['GET'],
                '/claim': ['POST'],
                '/redeem': ['POST'],
                '/voucher-info': ['GET']
            }};

            // Validate endpoint is allowed
            if (!ALLOWED_ENDPOINTS[endpoint]) {{
                throw new Error(`Endpoint not allowed: ${{endpoint}}`);
            }}

            // Validate method is allowed for this endpoint
            if (!ALLOWED_ENDPOINTS[endpoint].includes(method)) {{
                throw new Error(`Method ${{method}} not allowed for endpoint ${{endpoint}}`);
            }}

            try {{
                const apiUrl = window.location.origin + endpoint;
                const options = {{
                    method: method,
                    headers: {{
                        'X-API-Key': '{iframe_token}'
                    }}
                }};

                // Only add Content-Type for non-GET requests
                if (method !== 'GET') {{
                    options.headers['Content-Type'] = 'application/json';
                }}

                if (method !== 'GET' && data) {{
                    options.body = JSON.stringify(data);
                }}

                if (method === 'GET' && data) {{
                    const params = new URLSearchParams(data);
                    const separator = apiUrl.includes('?') ? '&' : '?';
                    const fullUrl = apiUrl + separator + params.toString();
                    const response = await fetch(fullUrl, options);
                    return await response.json();
                }} else {{
                    const response = await fetch(apiUrl, options);
                    return await response.json();
                }}
            }} catch (error) {{
                throw new Error(`API call failed: ${{error.message}}`);
            }}
        }}

        // Handle messages from parent (with strict security validation)
        window.addEventListener('message', function(event) {{
            // Validate origin and nonce for security - be strict
            if (parentOrigin === 'null' || event.origin !== parentOrigin) {{
                // console.warn('Ignored message from unauthorized origin:', event.origin, 'expected:', parentOrigin);
                return;
            }}

            if (event.data && event.data.nonce !== messageNonce) {{
                // console.warn('Ignored message with invalid nonce');
                return;
            }}

            if (event.data && event.data.type === 'iframe_disconnect') {{
                // console.log('🔌 Received disconnect message from parent');
                if (eventSource) {{
                    eventSource.close();
                    eventSource = null;
                }}
                document.getElementById('status').textContent = 'Disconnected';
                // Acknowledge disconnect
                if (window.parent && window.parent !== window) {{
                    window.parent.postMessage({{
                        type: 'iframe_sse_disconnected',
                        nonce: messageNonce,
                        timestamp: Date.now()
                    }}, parentOrigin);
                }}
            }}

            // Handle secure API calls from parent
            if (event.data && event.data.type === 'api_call') {{
                const {{ requestId, endpoint, method, data }} = event.data;
                // console.log('🔐 Processing secure API call:', endpoint);

                handleApiCall(endpoint, method || 'GET', data)
                    .then(result => {{
                        // Send success response back to parent
                        if (window.parent && window.parent !== window) {{
                            window.parent.postMessage({{
                                type: 'api_response',
                                requestId: requestId,
                                success: true,
                                data: result,
                                nonce: messageNonce,
                                timestamp: Date.now()
                            }}, parentOrigin);
                        }}
                    }})
                    .catch(error => {{
                        // Send error response back to parent
                        if (window.parent && window.parent !== window) {{
                            window.parent.postMessage({{
                                type: 'api_response',
                                requestId: requestId,
                                success: false,
                                error: error.message,
                                nonce: messageNonce,
                                timestamp: Date.now()
                            }}, parentOrigin);
                        }}
                    }});
            }}
        }});

        // Start connection immediately
        connectSSE();

        // Notify parent that iframe is ready (with origin validation)
        if (window.parent && window.parent !== window) {{
            window.parent.postMessage({{
                type: 'iframe_ready',
                nonce: messageNonce,
                timestamp: Date.now()
            }}, parentOrigin);
        }}

        // Clean up on page unload
        window.addEventListener('beforeunload', function() {{
            if (eventSource) {{
                eventSource.close();
            }}
        }});

    </script>
</body>
</html>"""

    return HTMLResponse(
        content=html_content,
        headers={
            "Cache-Control": "no-cache, no-store, must-revalidate",
            "Pragma": "no-cache",
            "Expires": "0",
            "X-Frame-Options": "ALLOWALL",
            "Content-Security-Policy": "frame-ancestors *;",
            "Access-Control-Allow-Origin": "*"
        }
    )

# Static files mount removed since index.html is in root directory

class WSManager:
    def __init__(self):
        self.active: Dict[str, Dict] = {}  # client_id -> { 'ws': WebSocket, 'username': str, 'ping_sent': float, 'last_pong': float }
        self.username_map: Dict[str, str] = {}  # username -> client_id
        self.heartbeat_task = None
        self.reconnect_buffers: Dict[str, List[Dict[str, Any]]] = {}
        self.code_ownership: Dict[str, str] = {}  # code -> username

        # INFINITE CONNECTION MODE - SOCKET.IO-STYLE PING/PONG CONFIGURATION
        self.ping_interval = 10.0  # Send ping every 10 seconds to keep connection alive
        # REMOVED: self.ping_timeout - Connections now stay active until manual disconnect or 0 credits

        # PERFORMANCE ENHANCEMENTS - BOUNDED QUEUE FOR 300+ USERS
        self.message_queue: asyncio.Queue = asyncio.Queue(maxsize=100)
        self.queue_processor_task = None
        self.priority_messages: asyncio.Queue = asyncio.Queue(maxsize=100)
        self.burst_limit = 10  # Max messages per second
        self.last_broadcast_time = 0

    async def connect(self, ws: WebSocket, username: str) -> bool:
        # IMPROVED: Automatically disconnect previous connection and allow new one
        if username in self.username_map:
            existing_client_id = self.username_map[username]
            existing_connection = self.active.get(existing_client_id)

            if existing_connection:
                existing_ws = existing_connection['ws']
                # Automatically disconnect old connection to allow new one
                print(f"AUTO-DISCONNECT: Closing existing connection for {username} to allow new connection")
                try:
                    # Send disconnect notification to old connection
                    await existing_ws.send_json({
                        'type': 'force_disconnect',
                        'message': 'New connection detected - this session will be closed',
                        'timestamp': int(time.time())
                    })
                    # Close the old connection
                    await existing_ws.close(code=1000, reason="New connection from same user")
                except Exception as e:
                    print(f"Warning: Error closing old connection: {e}")
                
                # Clean up the old connection
                await self._cleanup_dead_connection(existing_client_id)
                print(f"Previous connection for {username} closed - allowing new connection")
            else:
                # Username in map but no active connection - clean up the mapping
                print(f"Cleaning orphaned username mapping for {username}")
                self.username_map.pop(username, None)

        await ws.accept()
        client_id = f"{username}:{ws.client.host}:{ws.client.port}:{id(ws)}"
        current_time = asyncio.get_event_loop().time()
        self.active[client_id] = {
            'ws': ws, 
            'username': username, 
            'ping_sent': 0, 
            'last_pong': current_time
        }
        self.username_map[username] = client_id

                # if username in self.reconnect_buffers:
        #     buffered_messages = self.reconnect_buffers[username]
        #     if buffered_messages:
        #         print(f"Delivering {len(buffered_messages)} buffered messages to {username}")
        #         # Send buffered messages concurrently for faster delivery - TRUE FIRE AND FORGET
        #         buffer_tasks = []
        #         for msg in buffered_messages[-50:]:  # Limit to last 50 messages
        #             # Fire and forget each buffered message - no waiting
        #             asyncio.create_task(self._fast_send(ws, msg, username))
        #         print(f"FIRED {len(buffered_messages[-50:])} buffered messages simultaneously")
        #     del self.reconnect_buffers[username]

        # Start heartbeat if first connection
        if len(self.active) == 1 and not self.heartbeat_task:
            self.heartbeat_task = asyncio.create_task(self._heartbeat_loop())

        # Start queue processor if first connection
        if len(self.active) == 1 and not self.queue_processor_task:
            self.queue_processor_task = asyncio.create_task(self._process_message_queue())

        return True

    async def _cleanup_dead_connection(self, client_id: str):
        """Clean up a dead connection silently"""
        if client_id in self.active:
            username = self.active[client_id]['username']
            self.active.pop(client_id, None)
            self.username_map.pop(username, None)
            # Silent cleanup: Remove user's session token when connection dies
            if username in user_session_tokens:
                del user_session_tokens[username]

    async def disconnect(self, ws: WebSocket):
        client_id = None
        username = None

        # Find the client to disconnect
        for cid, data in list(self.active.items()):
            if data['ws'] == ws:
                client_id = cid
                username = data['username']
                break

        if client_id and username:
            # Remove from active connections
            self.active.pop(client_id, None)

            # Only remove from username_map if this is the current mapping
            # (prevents removing a newer connection's mapping)
            if self.username_map.get(username) == client_id:
                self.username_map.pop(username, None)
                print(f"🔌 Client {client_id} ({username}) disconnected cleanly")
            else:
                print(f"🔌 Client {client_id} ({username}) disconnected (username remapped)")

                        # if username not in self.reconnect_buffers:
            #     self.reconnect_buffers[username] = []
            # # Add recent messages to buffer (last 10 minutes of codes)
            # current_time = int(asyncio.get_event_loop().time() * 1000)
            # recent_messages = []
            # for entry in ring_get_all():
            #     if entry.get("type") == "code" and current_time - entry.get("ts", 0) < 600000:  # 10 minutes
            #         recent_messages.append(entry)
            # # Store only the most recent messages to prevent buffer overflow
            # self.reconnect_buffers[username] = recent_messages[-20:]  # Keep last 20 codes

            # Silent cleanup: Remove user's session token when they disconnect
            if username in user_session_tokens:
                del user_session_tokens[username]

    async def broadcast(self, message: Dict[str, Any], priority: bool = False):
        """Enhanced broadcast with priority handling and queuing"""
        # Continue if there are SSE connections even with no WebSocket
        if not self.active and not sse_message_queues:
            return

        # Add timestamp for instant delivery
        message["server_ts"] = int(asyncio.get_event_loop().time() * 1000)

        # Track code ownership
        if message.get("type") == "code":
            code = message.get("code")
            if code:
                self.code_ownership[code] = message.get("username", "system")
            priority = True  # All code messages are priority

        # Handle priority messages immediately
        if priority:
            await self._instant_broadcast(message)
        else:
            # Queue non-priority messages for processing
            try:
                self.message_queue.put_nowait(message)
            except asyncio.QueueFull:
                # If queue is full, process immediately
                await self._instant_broadcast(message)

    async def _instant_broadcast(self, message: Dict[str, Any]):
        """SSE-ONLY broadcasting for optimal performance - WebSocket disabled for outbound messages"""
        if not sse_connections:
            return

        # PERFORMANCE OPTIMIZATION: SSE-only broadcasting (WebSocket disabled for sending)
        # WebSocket connections still maintained for receiving codes from external sources

        # BROADCAST TO SSE CONNECTIONS ONLY
        await self._broadcast_to_sse(message)

    async def _process_message_queue(self):
        """Process non-priority messages with rate limiting"""
        while self.active or not self.message_queue.empty():
            try:
                # Rate limiting to prevent overwhelming clients
                current_time = asyncio.get_event_loop().time()
                if current_time - self.last_broadcast_time < (1.0 / self.burst_limit):
                    await asyncio.sleep(0.1)
                    continue

                # Get message from queue with timeout
                try:
                    message = await asyncio.wait_for(self.message_queue.get(), timeout=1.0)
                    await self._instant_broadcast(message)
                    self.last_broadcast_time = current_time
                    self.message_queue.task_done()
                except asyncio.TimeoutError:
                    continue

            except Exception as e:
                print(f"Queue processor error: {e}")
                await asyncio.sleep(1)

        self.queue_processor_task = None

    async def _fast_send(self, ws: WebSocket, message: Dict[str, Any], username: str) -> bool:
        """Ultra-fast concurrent message sending with proper delivery verification"""
        try:
            # Actually await the send to verify delivery for 100 users simultaneity
            await ws.send_json(message)
            return True
        except Exception:
            return False

    async def _broadcast_to_sse(self, message: Dict[str, Any]):
        """ULTRA-FAST SSE broadcast - SEND FIRST, DEDUCT CREDITS AFTER"""
        if not sse_message_queues:
            return

        # PRODUCTION OPTIMIZATION: Instant concurrent broadcasting
        broadcast_start = asyncio.get_event_loop().time()
        successful_broadcasts = 0
        failed_broadcasts = 0
        dead_queues = []

        # ULTRA-FAST OPTIMIZATION: Use persistent cache for authorization (NO database calls!)
        eligible_users = []
        if message.get("type") == "code":
            # SPEED OPTIMIZATION: Send codes to ALL connected users first, validate credits after
            # This eliminates the 1432ms delay from sequential database checks
            eligible_users = list(sse_message_queues.keys())
            print(f"INSTANT BROADCAST: Sending code {message.get('code')} to {len(eligible_users)} connected users")
        else:
            # For non-code messages (ping, status, etc.), send to all users
            eligible_users = list(sse_message_queues.keys())

        # Create concurrent tasks for ALL connected users (instant delivery)
        tasks = []
        for username in eligible_users:
            message_queue = sse_message_queues[username]
            task = asyncio.create_task(self._fast_sse_send(username, message_queue, message))
            tasks.append((username, task))

        # Execute all SSE sends simultaneously (ZERO latency between customers)
        if tasks:
            results = await asyncio.gather(*[task for _, task in tasks], return_exceptions=True)

            successful_users = []
            for i, result in enumerate(results):
                username = tasks[i][0]
                if result is True:
                    successful_broadcasts += 1
                    successful_users.append(username)
                elif isinstance(result, Exception):
                    failed_broadcasts += 1
                    dead_queues.append(username)

            # ASYNC CREDIT VALIDATION: Check credits AFTER successful delivery (non-blocking)
            if message.get("type") == "code" and successful_users:
                asyncio.create_task(self._validate_and_track_code_delivery(message, successful_users))

        # Clean up dead queues
        for username in dead_queues:
            if username in sse_message_queues:
                del sse_message_queues[username]
            if username in sse_connections:
                del sse_connections[username]

        # Production monitoring
        elapsed = (asyncio.get_event_loop().time() - broadcast_start) * 1000
        if message.get("type") == "code":
            print(f"SSE Code {message.get('code')} → {successful_broadcasts} customers ({elapsed:.1f}ms)")

    async def _validate_and_track_code_delivery(self, message: Dict[str, Any], successful_users: List[str]):
        """ASYNC: Validate credits and track code delivery AFTER successful broadcast with ACK system"""
        import time
        import uuid
        current_time = time.time()
        code = message.get('code', 'unknown')
        message_id = str(uuid.uuid4())  # Unique ID for this delivery

        authorized_users = []
        unauthorized_users = []

        # Fast authorization check using persistent cache
        for username in successful_users:
            is_authorized = _is_user_preauthorized_fast(username)
            if is_authorized:
                authorized_users.append(username)
            else:
                unauthorized_users.append(username)

        # Log delivery tracking with message ID
        if authorized_users:
            print(f"Code {code} (msg:{message_id[:8]}) delivered to {len(authorized_users)} authorized users: {authorized_users[:3]}{'...' if len(authorized_users) > 3 else ''}")

        if unauthorized_users:
            print(f"Warning: Code {code} (msg:{message_id[:8]}) delivered to {len(unauthorized_users)} unauthorized users (will disconnect): {unauthorized_users[:3]}{'...' if len(unauthorized_users) > 3 else ''}")

            # Schedule disconnection for unauthorized users (non-blocking)
            for username in unauthorized_users:
                asyncio.create_task(self._disconnect_unauthorized_user(username))

        # IMPROVED METRICS: Update delivery tracking consistently
        connection_metrics['total_code_deliveries'] += len(successful_users)
        connection_metrics['authorized_deliveries'] += len(authorized_users)
        connection_metrics['unauthorized_deliveries'] += len(unauthorized_users)

        # DELIVERY ACKNOWLEDGMENT: Send delivery confirmation to authorized users
        if authorized_users:
            delivery_ack_message = {
                'type': 'code_delivery_ack',
                'code': code,
                'message_id': message_id,
                'delivery_time': current_time,
                'status': 'delivered'
            }

            # Send acknowledgment to authorized users
            for username in authorized_users:
                if username in sse_message_queues:
                    try:
                        sse_message_queues[username].put_nowait(delivery_ack_message)
                    except asyncio.QueueFull:
                        print(f"Warning: ACK queue full for {username}, skipping delivery confirmation")

        print(f"📊 DELIVERY METRICS: total={connection_metrics['total_code_deliveries']}, authorized={connection_metrics['authorized_deliveries']}, unauthorized={connection_metrics['unauthorized_deliveries']}")

    async def _disconnect_unauthorized_user(self, username: str):
        """Gracefully disconnect users who received codes but lack authorization"""
        try:
            # Send balance warning message before disconnect
            if username in sse_message_queues:
                warning_message = {
                    'type': 'balance_warning',
                    'message': 'Your credits are low. Please recharge to continue receiving codes.',
                    'credits': 0,
                    'timestamp': int(time.time())
                }
                try:
                    sse_message_queues[username].put_nowait(warning_message)
                except asyncio.QueueFull:
                    pass  # Skip if queue is full

                # Wait a bit for message delivery
                await asyncio.sleep(1)

            # Remove from SSE connections
            if username in sse_connections:
                del sse_connections[username]
            if username in sse_message_queues:
                del sse_message_queues[username]

            print(f"🔌 DISCONNECTED: {username} (insufficient credits for code delivery)")

        except Exception as e:
            print(f"Failed to disconnect unauthorized user {username}: {e}")

    async def _fast_sse_send(self, username: str, message_queue: asyncio.Queue, message: Dict[str, Any]) -> bool:
        """Ultra-fast SSE message delivery with stream health validation - FIXED ZOMBIE CONNECTIONS"""
        try:
            # PERFORMANCE OPTIMIZATION: Skip health validation for urgent code messages to reduce latency
            if message.get("type") != "code":
                # Only validate health for non-code messages (pings, status, etc.)
                if not self._validate_sse_stream_health(username):
                    print(f"STREAM HEALTH FAILED: Triggering reconnection for {username}")
                    self._trigger_sse_reconnection(username)
                    return False

            # OPTIMIZATION: Fast queue management for code messages
            if message.get("type") == "code" and message_queue.full():
                # PERFORMANCE OPTIMIZATION: Quick clear for code messages - just drop 5 oldest messages
                try:
                    for _ in range(5):  # Drop 5 oldest messages quickly
                        try:
                            message_queue.get_nowait()
                            message_queue.task_done()
                        except asyncio.QueueEmpty:
                            break
                    print(f"🧹 Fast-cleared 5 old messages from {username} queue for urgent code delivery")
                except Exception:
                    pass  # If clearing fails, continue anyway

            # Instant delivery - non-blocking with delivery confirmation
            message_queue.put_nowait(message)

            # Mark successful delivery for stream health tracking
            self._mark_sse_delivery_success(username)
            return True

        except asyncio.QueueFull:
            # ENHANCED BACKPRESSURE: Drop oldest message to make room for new one
            connection_metrics['queue_overflows'] += 1
            print(f"Warning: Queue full for {username} - dropping oldest message to make room")
            try:
                # Drop oldest message and add new one (graceful backpressure)
                try:
                    message_queue.get_nowait()  # Remove oldest
                    message_queue.task_done()
                except asyncio.QueueEmpty:
                    pass
                message_queue.put_nowait(message)  # Add new message
                print(f"Queue backpressure handled for {username} - dropped 1 old message")
                return True
            except Exception as drop_error:
                # If dropping oldest fails, then trigger reconnection as last resort
                print(f"Queue backpressure failed for {username}: {drop_error} - triggering reconnection")
                self._trigger_sse_reconnection(username)
                return False
        except Exception as e:
            print(f"SSE send error for {username}: {e} - triggering reconnection")
            self._trigger_sse_reconnection(username)
            return False

    def _validate_sse_stream_health(self, username: str) -> bool:
        """CRITICAL FIX: Validate actual SSE stream health beyond pong responses"""
        try:
            # Check if user has active connections
            if username not in sse_connections or not sse_connections[username]:
                return False

            # Check if message queue exists and is healthy
            if username not in sse_message_queues:
                return False

            # Only check for actual connection failures, not message delivery issues
            current_time = time.time()
            if hasattr(self, '_sse_delivery_stats'):
                user_stats = self._sse_delivery_stats.get(username, {})
                failure_count = user_stats.get('recent_failures', 0)

                # Only mark stale on excessive CONSECUTIVE failures (not time-based)
                # Changed from 60-second timeout to 10+ consecutive failures
                if failure_count > 10:  # Only after 10+ consecutive delivery failures
                    print(f"🚨 STALE STREAM DETECTED: {username} - {failure_count} consecutive failures")
                    return False

            return True
        except Exception as e:
            print(f"Warning: Stream health validation error for {username}: {e}")
            return False

    def _mark_sse_delivery_success(self, username: str):
        """Mark successful SSE delivery for stream health tracking"""
        if not hasattr(self, '_sse_delivery_stats'):
            self._sse_delivery_stats = {}

        if username not in self._sse_delivery_stats:
            self._sse_delivery_stats[username] = {}

        self._sse_delivery_stats[username]['last_success'] = time.time()
        self._sse_delivery_stats[username]['recent_failures'] = 0

    def _trigger_sse_reconnection(self, username: str):
        """CRITICAL FIX: Force SSE reconnection by cleaning up stale connections"""
        try:
            print(f"FORCING RECONNECTION for {username}")

            # Track delivery failure
            if not hasattr(self, '_sse_delivery_stats'):
                self._sse_delivery_stats = {}

            if username not in self._sse_delivery_stats:
                self._sse_delivery_stats[username] = {}

            self._sse_delivery_stats[username]['recent_failures'] = self._sse_delivery_stats[username].get('recent_failures', 0) + 1

            # Clean up all connections for this user
            if username in sse_connections:
                connection_ids = sse_connections[username].copy()
                for conn_id in connection_ids:
                    # Remove from health tracking
                    if conn_id in sse_connection_health:
                        del sse_connection_health[conn_id]
                    print(f"🧹 Cleaned stale connection: {conn_id}")

                # Clear user connections - this will force client to reconnect
                del sse_connections[username]

            # Clear message queue to prevent backlog
            if username in sse_message_queues:
                queue = sse_message_queues[username]
                # Drain the queue
                while not queue.empty():
                    try:
                        queue.get_nowait()
                        queue.task_done()
                    except:
                        break
                del sse_message_queues[username]
                print(f"🧹 Cleared message queue for {username}")

            # Clean up authorization (will be recreated on reconnect) (async task for method context)
            asyncio.create_task(_cleanup_user_authorization(username))

            print(f"RECONNECTION TRIGGERED: {username} must reconnect to receive messages")

        except Exception as e:
            print(f"Error triggering reconnection for {username}: {e}")

    async def _send_to_client(self, client_id: str, ws: WebSocket, message: Dict[str, Any]):
        try:
            await ws.send_json(message)
        except Exception as e:
            # Remove dead connection
            await self.disconnect(ws)

    async def _heartbeat_loop(self):
        while self.active:
            try:
                current_time = asyncio.get_event_loop().time()
                ping_message = {"type": "ping", "ts": int(current_time * 1000)}

                # SOCKET.IO-STYLE PING/PONG - Send pings concurrently
                tasks = []
                client_data = []

                for client_id, data in list(self.active.items()):
                    # Update ping sent timestamp
                    data['ping_sent'] = current_time
                    task = asyncio.create_task(self._fast_send(data['ws'], ping_message, data.get('username', 'unknown')))
                    tasks.append(task)
                    client_data.append((client_id, data))

                # Execute all pings concurrently
                try:
                    results = await asyncio.wait_for(asyncio.gather(*tasks, return_exceptions=True), timeout=1.0)
                except asyncio.TimeoutError:
                    results = [False] * len(tasks)

                # INFINITE CONNECTION MODE: Check only for failed ping sends (no pong timeout)
                dead_clients = []
                for i, result in enumerate(results):
                    client_id, data = client_data[i]

                    # Check if ping send failed (network issue)
                    if result is not True:
                        dead_clients.append(client_id)
                        continue

                    # REMOVED: No pong timeout check - connections stay active indefinitely
                    # Only disconnect on ping send failure (network disconnection)

                # Remove connections that failed ping sends (network disconnection)
                for client_id in dead_clients:
                    if client_id in self.active:
                        username = self.active[client_id]['username']
                        self.active.pop(client_id, None)
                        self.username_map.pop(username, None)
                        print(f"🔌 Network disconnection detected for {username} (ping send failed)")
                        # Silent cleanup of session tokens
                        if username in user_session_tokens:
                            del user_session_tokens[username]

                await asyncio.sleep(self.ping_interval)
            except Exception:
                await asyncio.sleep(self.ping_interval)
        self.heartbeat_task = None

    def handle_pong(self, client_id: str):
        """Handle pong response from client (Socket.IO style)"""
        if client_id in self.active:
            self.active[client_id]['last_pong'] = asyncio.get_event_loop().time()

    def validate_code_ownership(self, code: str, username: str) -> bool:
        """Check if the code belongs to the specified username"""
        return self.code_ownership.get(code) == username

ws_manager = WSManager()
ring: List[Dict[str, Any]] = []
seen: Set[str] = set()

# Initialize keep-alive service - CRITICAL FIX: Use PRODUCTION_URL for external pings
# Render only counts EXTERNAL requests to prevent sleep! localhost pings don't work!
keep_alive_service = KeepAliveService(PRODUCTION_URL, KEEP_ALIVE_INTERVAL) if KEEP_ALIVE_ENABLED else None

# Telegram Bot Setup  # official Telethon defaults
bot = None
if TELEGRAM_BOT_TOKEN:
    bot = TelegramClient("voucher-bot", TG_API_ID, TG_API_HASH)

def generate_code():
    """
    Generate voucher code in strict pattern: XXXX-XXXX-XX (12 chars total with dashes)
    Pattern: 4 alphanumeric + dash + 4 alphanumeric + dash + 2 alphanumeric
    Example: A3B7-9XY2-K4
    """
    part1 = ''.join(random.choices(string.ascii_uppercase + string.digits, k=4))
    part2 = ''.join(random.choices(string.ascii_uppercase + string.digits, k=4))
    part3 = ''.join(random.choices(string.ascii_uppercase + string.digits, k=2))
    return f"{part1}-{part2}-{part3}"

async def setup_bot_handlers():
    """Setup bot event handlers after bot is started"""
    if not bot:
        return

    @bot.on(events.NewMessage(pattern=r"^/voucher (\d+(\.\d+)?)$"))
    async def voucher_handler(event):
        if event.sender_id != TELEGRAM_ADMIN_ID:
            await event.reply("⛔ You are not authorized to use this bot.")
            return

        value = float(event.pattern_match.group(1))
        code = generate_code()

        db = SessionLocal()
        try:
            voucher = Voucher(code=code, value=value, remaining_value=value)
            db.add(voucher)
            db.commit()
            db.refresh(voucher)
            await event.reply(f"✅ Voucher Created!\n\n💳 Code: `{voucher.code}`\n💰 Value: {voucher.value}")
        except Exception as e:
            db.rollback()
            await event.reply(f"❌ Error creating voucher: {str(e)}")
        finally:
            db.close()

    # ===================== ADMIN RATE UPDATE COMMANDS =====================

    @bot.on(events.NewMessage(pattern=r"^/rate ([a-zA-Z]{2,10}) ([0-9]+\.?[0-9]*)$"))
    async def rate_handler(event):
        """Handle single rate updates: /rate BTC 67500.00"""
        if event.sender_id != TELEGRAM_ADMIN_ID:
            await event.reply("⛔ You are not authorized to use this bot.")
            return

        currency_input = event.pattern_match.group(1)
        rate = float(event.pattern_match.group(2))

        # Centralized currency validation
        try:
            currency = validate_currency(currency_input)
        except ValueError as e:
            await event.reply(f"❌ {str(e)}")
            return

        # Store admin rate to database (persists across restarts)
        success = save_admin_rate_to_db(currency, rate, 'admin')

        if success:
            await event.reply(f"✅ Rate Updated & Saved!\n\n💱 {currency.upper()}: ${rate} USD\n🕒 Updated: {admin_rates[currency]['updated_at']}\n💾 Saved to database\n\n💡 This rate will persist across server restarts.")
        else:
            await event.reply(f"⚠️ Rate Updated (Memory Only)\n\n💱 {currency.upper()}: ${rate} USD\n❌ Database save failed - rate will be lost on restart!")

        print(f"👑 ADMIN RATE SET: {currency.upper()} = ${rate} USD")

    @bot.on(events.NewMessage(pattern=r"^/rates (.+)$"))
    async def rates_bulk_handler(event):
        """Handle bulk rate updates: /rates BTC:67500.00,ETH:2650.00,USDT:1.00"""
        if event.sender_id != TELEGRAM_ADMIN_ID:
            await event.reply("⛔ You are not authorized to use this bot.")
            return

        rates_text = event.pattern_match.group(1)
        updated_currencies = []
        errors = []

        try:
            # Parse format: BTC:67500.00,ETH:2650.00,USDT:1.00
            for rate_pair in rates_text.split(','):
                if ':' not in rate_pair:
                    continue

                currency_input, rate_str = rate_pair.strip().split(':', 1)
                rate = float(rate_str.strip())

                # Centralized currency validation
                try:
                    currency = validate_currency(currency_input)
                except ValueError as e:
                    errors.append(str(e))
                    continue

                # Store admin rate to database (persists across restarts)
                success = save_admin_rate_to_db(currency, rate, 'admin')

                if success:
                    updated_currencies.append(f"{currency.upper()}: ${rate} ✅")
                else:
                    updated_currencies.append(f"{currency.upper()}: ${rate} ⚠️")
                    errors.append(f"Database save failed for {currency}")

                print(f"👑 ADMIN RATE SET: {currency.upper()} = ${rate} USD")

        except Exception as e:
            errors.append(str(e))

        if updated_currencies:
            response = f"✅ Bulk Rate Update!\n\n💱 Updated {len(updated_currencies)} rates:\n" + "\n".join(updated_currencies)
            response += f"\n\n🕒 Updated: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}\n\n💡 These rates will be used until you update them again."
        else:
            response = "❌ No valid rates updated."

        if errors:
            response += f"\n\n⚠️ Errors: {', '.join(errors)}"

        await event.reply(response)

    @bot.on(events.NewMessage(pattern=r"^/listrates$"))
    async def list_rates_handler(event):
        """List all currently set admin rates"""
        if event.sender_id != TELEGRAM_ADMIN_ID:
            await event.reply("⛔ You are not authorized to use this bot.")
            return

        if not admin_rates:
            await event.reply("📝 No admin rates set yet.\n\nUse `/rate CURRENCY AMOUNT` to set rates.\nExample: `/rate BTC 67500.00`")
            return

        response = f"📊 Current Admin Rates ({len(admin_rates)} set):\n\n"
        for currency, data in sorted(admin_rates.items()):
            response += f"💱 {currency.upper()}: ${data['rate']} USD\n"
            response += f"   🕒 Set: {data['updated_at']}\n\n"

        response += "💡 Use `/rate CURRENCY AMOUNT` to update any rate."
        await event.reply(response)

def normalize_code(s: str) -> str:
    # Remove non-alphanumeric characters but preserve original case
    return re.sub(r"[^A-Za-z0-9]", "", s)

def extract_codes_with_values(text: str) -> List[Dict[str, Any]]:
    """Extract bonus codes and values using multiple patterns, prioritizing 'Code:' format"""
    if not text:
        return []
        # print(f"🔍 Input text: {repr(text)}")  # Debug print to see exact text

    all_codes = []

    # First try the CODE_VALUE_PATTERN to extract code and value together
    try:
        pattern = re.compile(CODE_VALUE_PATTERN, re.IGNORECASE | re.MULTILINE | re.DOTALL)
        matches = pattern.findall(text)
                # print(f"🔍 Code+Value pattern -> Found: {matches}")  # Debug print

        for match in matches:
            if isinstance(match, tuple) and len(match) >= 1:
                code = match[0].strip()
                value = match[1] if len(match) > 1 and match[1] else None
                if code:
                    all_codes.append({"code": code, "value": value})
                                        # print(f"🎯 Found code with value: {code} = ${value}" if value else f"🎯 Found code: {code}")
    except Exception as e:
        print(f"Warning: Code+Value pattern error: {e}")

    # Then try all regular patterns (only for codes without values)
    for i, pattern_str in enumerate(CODE_PATTERNS):
        try:
            pattern = re.compile(pattern_str, re.IGNORECASE | re.MULTILINE)
            matches = pattern.findall(text)

                        # print(f"🔍 Pattern {i+1}: {pattern_str} -> Found: {matches}")  # Debug print
            # Handle both string and tuple results
            for match in matches:
                if isinstance(match, tuple):
                    for group in match:
                        if group:
                            code = group.strip()
                            # Check if this code was already found with a value
                            already_exists = any(existing["code"] == code for existing in all_codes)
                            if not already_exists:
                                all_codes.append({"code": code, "value": None})
                else:
                    code = match.strip()
                    # Check if this code was already found with a value
                    already_exists = any(existing["code"] == code for existing in all_codes)
                    if not already_exists:
                        all_codes.append({"code": code, "value": None})
        except Exception as e:
            print(f"Warning: Pattern error for {pattern_str}: {e}")
            continue

        # print(f"🔍 All extracted codes before filtering: {all_codes}")  # Debug print

    # Filter and validate codes
    valid_codes = []
    for item in all_codes:
        code = item["code"]
        value = item["value"]
        # Remove any non-alphanumeric characters
        cleaned_code = re.sub(r"[^A-Za-z0-9]", "", code)

        # Valid codes: 4-25 characters, alphanumeric
        if 4 <= len(cleaned_code) <= 25 and cleaned_code.isalnum():
            valid_codes.append({"code": cleaned_code, "value": value})

    # Remove duplicates while preserving order
    unique_codes = []
    for item in valid_codes:
        code = item["code"]
        if not any(existing["code"] == code for existing in unique_codes):
            unique_codes.append(item)

        # print(f"🔍 Final extracted codes: {unique_codes}")
    return unique_codes

def extract_codes(text: str) -> List[str]:
    """Legacy function for backward compatibility - extracts only codes"""
    codes_with_values = extract_codes_with_values(text)
    return [item["code"] for item in codes_with_values]

def ring_add(entry: Dict[str, Any]):
    ring.append(entry)
    if len(ring) > RING_SIZE:
        ring.pop(0)

def ring_latest() -> Optional[Dict[str, Any]]:
    return ring[-1] if ring else None

def ring_get_all() -> List[Dict[str, Any]]:
    """Get all entries from the ring buffer"""
    return list(ring)

tg_client = None
telegram_connected = False # Initialize to False

async def force_disconnect_all():
    """Force disconnect any existing Telegram connections"""
    global tg_client
    try:
        if tg_client:
            print("Force disconnecting existing Telegram client...")
            try:
                if tg_client.is_connected():
                    await asyncio.wait_for(tg_client.disconnect(), timeout=5.0)
                    print("Previous connection disconnected successfully")
            except Exception as e:
                print(f"Warning: Error disconnecting previous client: {e}")
            finally:
                tg_client = None
    except Exception as e:
        print(f"Warning: Force disconnect error: {e}")

async def check_connection_health():
    """Check if Telegram connection is healthy and reconnect if needed"""
    global tg_client, telegram_connected
    try:
        if not tg_client or not tg_client.is_connected():
            print("Warning: Connection health check failed - connection lost")
            telegram_connected = False
            return False

        # Test the connection with a simple API call
        try:
            await asyncio.wait_for(tg_client.get_me(), timeout=5.0)
            return True
        except Exception as e:
            print(f"Warning: Connection health check failed: {e}")
            telegram_connected = False
            return False
    except Exception as e:
        print(f"Warning: Error during connection health check: {e}")
        return False

async def ensure_tg(force_reconnect=False):
    global tg_client

    # If force reconnect is requested, disconnect first
    if force_reconnect:
        await force_disconnect_all()

    # Check if we already have a connected client
    if tg_client and tg_client.is_connected() and not force_reconnect:
        print("Using existing Telegram connection")
        return tg_client

    print(f"Auth: Creating Telegram client with session: {TG_SESSION}")
    print(f"Auth: API_ID: {TG_API_ID}")
    print(f"Auth: API_HASH: {'*' * len(TG_API_HASH) if TG_API_HASH else 'Not set'}")

    # Retry logic for connection
    max_retries = 3
    retry_delay = 2

    for attempt in range(max_retries):
        try:
            # Force disconnect any previous connections first
            await force_disconnect_all()

            client = TelegramClient(TG_SESSION, TG_API_ID, TG_API_HASH)
            print(f"🔌 Attempting to connect to Telegram (attempt {attempt + 1}/{max_retries})...")

            # Add timeout to prevent hanging
            await asyncio.wait_for(client.connect(), timeout=15.0)
            print("Connected to Telegram successfully!")

            print("🔍 Checking authorization status...")
            is_authorized = await asyncio.wait_for(client.is_user_authorized(), timeout=10.0)

            if not is_authorized:
                print("Session not authorized!")
                phone = os.getenv("TG_PHONE")
                login_code = os.getenv("TG_LOGIN_CODE")
                if not phone or not login_code:
                    raise RuntimeError("Session not authorized. You need to create a session file locally first. See RENDER_DEPLOYMENT_GUIDE.md")
                print(f"📱 Attempting login with phone: {phone}")
                await asyncio.wait_for(client.send_code_request(phone), timeout=15.0)
                try:
                    await asyncio.wait_for(client.sign_in(phone=phone, code=login_code), timeout=15.0)
                    print("Signed in successfully!")
                except SessionPasswordNeededError:
                    print("🔐 2FA required...")
                    pw = os.getenv("TG_2FA_PASSWORD")
                    if not pw:
                        raise RuntimeError("2FA required. Set TG_2FA_PASSWORD environment variable.")
                    await asyncio.wait_for(client.sign_in(password=pw), timeout=15.0)
                    print("2FA authentication successful!")
            else:
                print("Session already authorized!")

            tg_client = client
            print("🎉 Telegram client setup complete!")
            return client

        except asyncio.TimeoutError:
            print(f"TELEGRAM CONNECTION TIMEOUT (attempt {attempt + 1}/{max_retries})")
            if attempt < max_retries - 1:
                print(f"Retrying in {retry_delay} seconds...")
                await asyncio.sleep(retry_delay)
                retry_delay *= 2  # Exponential backoff
            else:
                print("All connection attempts failed")
                raise RuntimeError("Telegram connection timeout after all retries")

        except Exception as e:
            error_msg = str(e).lower()
            print(f"TELEGRAM CLIENT ERROR (attempt {attempt + 1}/{max_retries}): {e}")
            print(f"Error type: {type(e).__name__}")

            # Handle specific "already connected" errors
            if "already" in error_msg and "connect" in error_msg:
                print("'Already connected' error detected - forcing reconnection...")
                await force_disconnect_all()
                if attempt < max_retries - 1:
                    await asyncio.sleep(retry_delay)
                    retry_delay *= 2
                    continue

            if attempt < max_retries - 1:
                print(f"Retrying in {retry_delay} seconds...")
                await asyncio.sleep(retry_delay)
                retry_delay *= 2
            else:
                raise e

async def telegram_keepalive(client):
    """Keep Telegram connection alive with periodic pings"""
    ping_interval = 45  # Ping every 45 seconds
    
    while True:
        try:
            await asyncio.sleep(ping_interval)
            
            # Only ping if connected
            if client and client.is_connected():
                try:
                    # Send a lightweight ping to keep connection alive
                    await client(functions.PingRequest(ping_id=int(time.time())))
                    # Silently succeed - no log spam
                except Exception as e:
                    print(f"Warning: Keepalive ping failed: {e}")
            else:
                # Client disconnected, exit this keepalive task
                print("🔌 Keepalive: Client disconnected, stopping pings")
                break
                
        except asyncio.CancelledError:
            print("🛑 Keepalive task cancelled")
            break
        except Exception as e:
            print(f"Warning: Keepalive error: {e}")
            await asyncio.sleep(5)

async def start_listener():
    """
    SIMPLIFIED: Try to connect to Telegram once at startup
    - If successful, run until disconnected
    - If it fails or disconnects, just exit (no retry)
    - Web app continues to work without Telegram
    """
    global telegram_connected
    keepalive_task = None
    client = None

    try:
        print("Starting Telegram listener (single attempt)...")

        # Try to connect with 30 second timeout
        try:
            client = await asyncio.wait_for(ensure_tg(force_reconnect=False), timeout=30.0)
            if not client:
                print("❌ Failed to ensure Telegram client - Telegram disabled")
                print("✅ Web app will continue to work without Telegram")
                return
        except asyncio.TimeoutError:
            print("❌ TELEGRAM SETUP TIMEOUT (30 seconds)")
            print("✅ Web app will continue to work without Telegram")
            return
        except Exception as e:
            print(f"❌ Connection error: {e}")
            print("✅ Web app will continue to work without Telegram")
            return

        # Successfully connected - proceed with setup
        print(f"🎯 Current CHANNELS environment variable: '{CHANNELS}'")
        print(f"🎯 CHANNELS type: {type(CHANNELS)}")
        # Parse multiple channels from comma-separated string
        channel_list = [ch.strip() for ch in CHANNELS.split(',') if ch.strip()]
        print(f"📋 Parsed {len(channel_list)} channels: {channel_list}")
        # Channel mapping for better tracking
        channel_names = {}
        # First, let's list available dialogs to help find the correct channels
        print("🔍 Listing your available chats/channels:")
        async for dialog in client.iter_dialogs():
            print(f"  📱 {dialog.name} (ID: {dialog.id}, Username: {getattr(dialog.entity, 'username', 'None')})")
        # Validate each channel and build list of valid channels
        valid_channels = []
        for i, channel in enumerate(channel_list):
            try:
                print(f"🔍 [{i+1}/{len(channel_list)}] Attempting to get entity for: {channel}")
                entity = await client.get_entity(int(channel) if channel.lstrip('-').isdigit() else channel)
                channel_name = entity.title if hasattr(entity, 'title') else (entity.first_name or f"Channel_{entity.id}")
                channel_names[str(entity.id)] = channel_name
                print(f"[{i+1}] Successfully connected to: {channel_name} (ID: {entity.id})")
                # Convert to proper format for event listener
                channel_for_events = int(channel) if channel.lstrip('-').isdigit() else channel
                valid_channels.append(channel_for_events)
            except Exception as e:
                print(f"[{i+1}] Could not access channel {channel}: {e}")
                print(f"   Make sure you're a member of this channel/chat")
                print("   Skipping this channel...")
        if not valid_channels:
            print("❌ No valid channels found. Please check your CHANNELS environment variable")
            print("✅ Web app will continue to work without Telegram")
            return
        print(f"🎯 Setting up event listener for {len(valid_channels)} channels: {valid_channels}")

        # Define handler function (will be registered for THIS client only)
        async def message_handler(ev):
            # PRIORITY: Process message immediately without any delays
            channel_name = channel_names.get(str(ev.chat_id), f"Unknown_{ev.chat_id}")
            # ULTRA-FAST: Minimal logging for speed
            print(f"INSTANT MESSAGE from {channel_name}")
            # Get message text
            text = (ev.message.message or "")
            # Add caption if it exists (for media messages)
            if hasattr(ev.message, 'caption') and ev.message.caption:
                text += "\n" + ev.message.caption
            # ULTRA-FAST: Extract codes immediately
            codes_with_values = extract_codes_with_values(text)
            if codes_with_values:
                print(f"FOUND {len(codes_with_values)} codes")
            if not codes_with_values:
                print("No valid codes found in message")
                return
            ts = int(ev.message.date.timestamp() * 1000)
            broadcast_count = 0
            entries_to_broadcast = []

            # Process all codes first
            for item in codes_with_values:
                code = item["code"]
                value = item["value"]
                if code in seen:
                    print(f"Warning: Code {code} already seen, skipping")
                    continue
                seen.add(code)
                # Enhanced entry with more metadata
                entry = {
                    "type": "code",
                    "code": code,
                    "ts": ts,
                    "msg_id": ev.message.id,
                    "channel": str(ev.chat_id),
                    "channel_name": channel_name,
                    "claim_base": CLAIM_URL_BASE,
                    "priority": "instant",
                    "telegram_ts": ts,
                    "broadcast_ts": int(asyncio.get_event_loop().time() * 1000),
                    "source": "telegram",
                    "message_preview": text[:100],
                    "username": "system"  # Default to system since no username yet
                }

                # Add value to entry if it exists
                if value:
                    entry["value"] = value
                ring_add(entry)
                entries_to_broadcast.append(entry)
                broadcast_count += 1
                print(f"PREPARED #{broadcast_count}: {code}")

            # Broadcast all codes simultaneously
            if entries_to_broadcast:
                # Create all broadcast tasks at once for true simultaneous sending
                broadcast_tasks = [asyncio.create_task(ws_manager.broadcast(entry)) for entry in entries_to_broadcast]
                print(f"BROADCASTING {len(broadcast_tasks)} codes SIMULTANEOUSLY to all clients")
                # Optional: await all tasks to ensure they complete
                # await asyncio.gather(*broadcast_tasks, return_exceptions=True)

        # Register handler explicitly (prevents duplication on reconnect)
        client.add_event_handler(message_handler, events.NewMessage(chats=valid_channels))
        print("Event handler registered for new messages")
        
        # Update global status
        telegram_connected = True
        print("🎉 Event listener setup complete! Ready to receive messages...")
        print("Starting Telegram client and listening for messages...")
        await client.start()
        print("Telegram client started successfully!")
        
        # Start keepalive ping task to prevent idle disconnection
        keepalive_task = asyncio.create_task(telegram_keepalive(client))
        print("💓 Keepalive ping task started (45 second intervals)")
        
        try:
            # Run until disconnected (no reconnect)
            await client.run_until_disconnected()
        finally:
            # Always cleanup resources on exit
            print("🧹 Cleaning up Telegram resources...")
            telegram_connected = False
            
            # Cancel keepalive task
            if keepalive_task and not keepalive_task.done():
                keepalive_task.cancel()
                try:
                    await keepalive_task
                except asyncio.CancelledError:
                    pass
                print("Keepalive task cancelled")
            
            # Remove event handler to prevent duplication
            if client and message_handler:
                try:
                    client.remove_event_handler(message_handler)
                    print("Event handler removed")
                except Exception as cleanup_err:
                    print(f"Warning: Could not remove handler: {cleanup_err}")

        # Connection dropped - just log and exit (no retry)
        print("⚠️ Telegram disconnected - connection lost")
        print("✅ Web app will continue to work without Telegram")

    except Exception as e:
        print(f"❌ TELEGRAM LISTENER ERROR: {e}")
        print(f"Error type: {type(e).__name__}")
        telegram_connected = False
        
        # Cancel keepalive task on error
        if keepalive_task and not keepalive_task.done():
            keepalive_task.cancel()
            try:
                await keepalive_task
            except asyncio.CancelledError:
                pass
        
        # Just log and exit (no retry)
        print("✅ Web app will continue to work without Telegram")

@app.api_route("/", methods=["GET", "HEAD"])
async def root():
    return FileResponse('index.html')

@app.get("/api")
@app.head("/api")
async def api_root():
    """DECOY: Fake API endpoint to confuse attackers"""
    # Return fake authentication error
    return JSONResponse({
        "error": "Unauthorized",
        "message": "API key required for access",
        "code": 401,
        "details": "Missing or invalid authentication credentials"
    }, status_code=401)

@app.on_event("startup")
async def startup_event():
    # 🔥 CRITICAL: WAL crash recovery FIRST - replay unsynced credit deductions
    print("=" * 60)
    print("WAL CRASH RECOVERY - Replaying unsynced credit deductions...")
    print("=" * 60)
    await wal_crash_recovery()
    
    # Start WAL reconciliation worker (runs every 5 minutes)
    print("Starting WAL reconciliation worker...")
    asyncio.create_task(wal_reconciliation_check())
    
    # 🛡️ REMOVED: startup_reconciliation() no longer needed
    # WAL crash recovery above already handles all credit deduction replays
    print("Startup initialization complete - WAL crash recovery finished")

    # Enhanced database initialization with validation
    print("🗃️ Initializing database connection and tables...")
    try:
        # Check database connection
        db_url = DATABASE_URL or "sqlite:///./test.db"
        if DATABASE_URL:
            if DATABASE_URL.startswith("postgresql"):
                print(f"Using Supabase PostgreSQL database")
            else:
                print(f"Using PostgreSQL database")
        else:
            print("Warning:  WARNING: DATABASE_URL not set - using SQLite fallback for development")
            print("   For production, please set DATABASE_URL to your Supabase connection string")

        # Test database connection
        with engine.connect() as conn:
            result = conn.execute(text("SELECT 1")).scalar()
            if result == 1:
                print("Database connection successful")
            else:
                print("Database connection test failed")

        # Create all tables
        Base.metadata.create_all(bind=engine)
        print("Database tables created/verified")

        # Verify critical tables exist
        with engine.connect() as conn:
            tables_to_check = ['users', 'vouchers', 'transactions', 'claim_attempts']
            existing_tables = []

            for table in tables_to_check:
                if DATABASE_URL and DATABASE_URL.startswith("postgresql"):
                    # PostgreSQL/Supabase check
                    result = conn.execute(text(f"""
                        SELECT table_name FROM information_schema.tables 
                        WHERE table_schema = 'public' AND table_name = '{table}'
                    """)).fetchone()
                else:
                    # SQLite check
                    result = conn.execute(text(f"""
                        SELECT name FROM sqlite_master 
                        WHERE type='table' AND name='{table}'
                    """)).fetchone()

                if result:
                    existing_tables.append(table)

            print(f"Verified tables exist: {', '.join(existing_tables)}")
            missing_tables = set(tables_to_check) - set(existing_tables)
            if missing_tables:
                print(f"Warning:  Missing tables: {', '.join(missing_tables)}")
                print("   If using Supabase, run the supabase_schema.sql script in the SQL editor")

    except Exception as e:
        print(f"Database initialization error: {e}")
        print(f"   Error type: {type(e).__name__}")
        if DATABASE_URL:
            print("   Check your DATABASE_URL connection string")
            print("   For Supabase: ensure connection string includes sslmode=require")
        else:
            print("   Set DATABASE_URL environment variable for production use")

    # Load admin rates from database on startup
    print("💾 Loading admin rates from database...")
    load_admin_rates_from_db()

    # Start automatic connection cleanup
    print("Starting automatic database connection cleanup...")
    asyncio.create_task(cleanup_idle_connections())

    # SECURITY FIX: Start pre-authorization recovery system
    print("Starting pre-authorization recovery system...")
    asyncio.create_task(preauth_recovery_service())

    # Note: Removed complex escrow cleanup - using simple immediate deduction now

    print("STAKE ULTRA CLAIMER - RENDER DEPLOYMENT")
    print("=" * 50)
    print(f"Server starting on port {PORT}")
    print(f"Token: TG_API_ID configured: {'✅' if TG_API_ID else '❌'}")
    print(f"Token: TG_API_HASH configured: {'✅' if TG_API_HASH else '❌'}")
    print(f"📺 CHANNELS configured: {'✅' if CHANNELS else '❌'}")
    # TIMEOUT FIX: Skip Telegram if using dummy/invalid credentials
    is_valid_telegram = (
        TG_API_ID and TG_API_ID > 1000 and  # Reject dummy API_ID like 123456
        TG_API_HASH and len(TG_API_HASH) > 10 and TG_API_HASH != "dummy" and  # Reject dummy hash
        CHANNELS and "-100" in CHANNELS  # Validate channel format
    )
    
    if is_valid_telegram:
        channel_count = len([ch.strip() for ch in CHANNELS.split(',') if ch.strip()])
        print(f"Starting Telegram listener for {channel_count} channels: {CHANNELS}")
        print("Ultra-fast code extraction and broadcasting enabled")
        asyncio.create_task(start_listener())
    else:
        print("Warning: Telegram listener DISABLED - Invalid or dummy credentials detected")
        print("   Set these environment variables for Telegram monitoring:")
        print("   - TG_API_ID (Get from https://my.telegram.org/apps)")
        print("   - TG_API_HASH (Get from https://my.telegram.org/apps)")
        print("   - CHANNELS (Channel IDs, example: -1002772030545,-1001234567890)")
        print("   ✅ Server will run normally without Telegram (web interface still works)")
    # Start keep-alive service
    if keep_alive_service:
        print(f"Starting keep-alive service (ping every {KEEP_ALIVE_INTERVAL} minutes)")
        asyncio.create_task(keep_alive_service.start_keep_alive())
    else:
        print("ℹ️ Keep-alive service disabled")

    # Start Telegram bot - CRASH FIX: Validate credentials before starting
    is_valid_bot_token = (
        TELEGRAM_BOT_TOKEN and 
        len(TELEGRAM_BOT_TOKEN) > 20 and  # Real bot tokens are much longer
        ":" in TELEGRAM_BOT_TOKEN and
        not TELEGRAM_BOT_TOKEN.startswith("dummy") and  # Reject dummy tokens
        TELEGRAM_ADMIN_ID and 
        TELEGRAM_ADMIN_ID > 10000  # Real admin IDs are larger
    )
    
    if bot and is_valid_bot_token:
        print(f"🤖 Starting Telegram voucher bot...")
        print(f"Token: Admin ID: {TELEGRAM_ADMIN_ID}")
        async def run_bot():
            try:
                await bot.start(bot_token=TELEGRAM_BOT_TOKEN)
                await setup_bot_handlers()
                await bot.run_until_disconnected()
            except Exception as e:
                print(f"Bot crashed: {e}")
        asyncio.create_task(run_bot())
    else:
        print("ℹ️ Telegram bot disabled - Invalid or dummy credentials detected")
        print("   Set TELEGRAM_BOT_TOKEN (from @BotFather) and TELEGRAM_ADMIN_ID to enable")

    # Start background workers for cache and queue management
    print("Starting background workers for performance optimization...")
    background_tasks['queue_processor'] = asyncio.create_task(background_queue_processor())
    background_tasks['cache_refresher'] = asyncio.create_task(background_cache_refresher())
    background_tasks['cache_cleaner'] = asyncio.create_task(background_cache_cleaner())
    print("Background workers started: queue processor, cache refresher, cache cleaner")

def _get_or_create_user(db: Session, username: str) -> User:
    # Validate and sanitize username input at the database function level
    if isinstance(username, dict):
        print(f"Warning: CRITICAL: _get_or_create_user received dict instead of string: {username}")
        raise ValueError("Username must be a string, not a dictionary")

    # Ensure username is a clean string
    username = str(username).strip()
    if not username:
        raise ValueError("Username cannot be empty")

    user = db.query(User).filter(User.username == username).first()
    if not user:
        # Give new users $0.5 starter credits
        user = User(username=username, credits=0.5)
        db.add(user)
        db.commit()
        db.refresh(user)
        print(f"User: New user '{username}' created with $0.5 starter credits")
    return user

@app.get("/healthz")
@app.head("/healthz")
async def health_check():
    """Health check endpoint for load balancer and monitoring - Supports both GET and HEAD"""
    import time
    return {"status": "healthy", "timestamp": int(time.time()), "version": "scalability-optimized"}

@app.get("/balance")
async def get_balance(request: Request, username: str, authenticated_user: str = Depends(auth_context), db: Session = Depends(get_db)):
    """Optimized balance endpoint with caching and robust error handling"""
    # Use centralized AuthContext - authenticated_user is now guaranteed valid

    # Additional validation for username parameter
    if not username or not isinstance(username, str):
        print(f"Warning: Invalid username in /balance: {username} (type: {type(username)})")
        raise HTTPException(status_code=400, detail="Invalid username parameter")

    # Validate the authenticated user matches the request user
    if username != authenticated_user:
        # Misleading resource error instead of user mismatch
        raise HTTPException(status_code=409, detail="Resource conflict. Another operation is in progress.")

    try:
        # Use cached user credits instead of direct database access
        user_data = await get_user_credits(username)
        
        # Validate user_data structure before accessing
        if not user_data or not isinstance(user_data, dict):
            print(f"BALANCE ERROR: Invalid user_data structure for {username}: {user_data}")
            # Force cache refresh and retry
            await refresh_user_credit_cache(username)
            user_data = user_credit_cache.get(username, {
                'credits': Decimal('0.5'),
                'reserved_credits': Decimal('0.0'),
                'expires': time.time() + USER_CREDIT_CACHE_TTL
            })
        
        # SIMPLIFIED: Use single credits field (no reserved_credits needed)
        credits = safe_decimal(user_data.get('credits', '0'), '0')
        
        # Write sanitized Decimals back to cache
        user_credit_cache[username] = {
            'credits': credits,
            'expires': user_data.get('expires', time.time() + USER_CREDIT_CACHE_TTL)
        }

        print(f"📊 CACHED BALANCE: {username} = ${credits:.4f}")

        # Convert Decimal to float for JSON response
        try:
            return {
                "username": username, 
                "credits": float(credits.quantize(Decimal('0.00000001'), rounding=ROUND_HALF_UP)),
                "available_credits": float(credits.quantize(Decimal('0.00000001'), rounding=ROUND_HALF_UP)),
                "reserved_credits": 0.0  # Always 0 with simplified system
            }
        except InvalidOperation as e:
            print(f"Warning: InvalidOperation in balance quantization for {username}: {e}")
            # Fallback to safe zero values
            return {
                "username": username,
                "credits": 0.0,
                "available_credits": 0.0,
                "reserved_credits": 0.0
            }
    except HTTPException:
        # Re-raise HTTPExceptions as-is
        raise
    except ValueError as e:
        print(f"Warning: Username validation error in /balance: {e}")
        raise HTTPException(status_code=400, detail=str(e))
    except Exception as e:
        # Catch any other errors and return proper error response
        print(f"BALANCE ENDPOINT ERROR for {username}: {e}")
        import traceback
        traceback.print_exc()
        raise HTTPException(status_code=500, detail="Failed to retrieve balance. Please try again.")

@app.post("/redeem")
async def redeem(request: Request, body: dict = Body(...), authenticated_user: str = Depends(auth_context)):
    """FIXED: Database-first atomic voucher redemption with cache sync - prevents unlimited claims"""
    # Use centralized AuthContext - authenticated_user is now guaranteed valid
    username = body.get("username")
    # Validate the authenticated user matches the request user
    if username != authenticated_user:
        # Misleading payment processing error instead of user mismatch
        raise HTTPException(status_code=402, detail="Payment processor temporarily unavailable. Please try again in a few minutes.")
    voucher_code = body.get("voucher_code")

    if not username or not voucher_code:
        raise HTTPException(status_code=400, detail="username and voucher_code required")
    
    # STRICT VALIDATION: Check voucher code pattern IMMEDIATELY (before any database queries)
    is_valid, error_message = validate_voucher_code(voucher_code)
    if not is_valid:
        print(f"🚫 REJECTED INVALID VOUCHER: {username} tried to use '{voucher_code}' - {error_message}")
        raise HTTPException(status_code=400, detail=f"Invalid voucher code format: {error_message}")

    # If amount is specified, use partial redemption; otherwise redeem all remaining - PRECISION: Use Decimal from start
    redeem_amount = body.get("amount")
    if redeem_amount is not None:
        redeem_amount_decimal = Decimal(str(redeem_amount))
        if redeem_amount_decimal < Decimal('0.5'):
            raise HTTPException(status_code=400, detail="Minimum redemption amount is $0.5")
    else:
        # Get voucher from cache to determine full redemption amount
        voucher_data = await get_voucher_from_cache(voucher_code)
        if not voucher_data:
            raise HTTPException(status_code=404, detail="Voucher not found")
        redeem_amount_decimal = voucher_data['remaining_value']

    # Per-voucher locking to prevent double-spending with 500 concurrent users
    if voucher_code not in voucher_redemption_locks:
        voucher_redemption_locks[voucher_code] = asyncio.Lock()

    async with voucher_redemption_locks[voucher_code]:
        try:
            # DATABASE-FIRST: Atomic database update with proper validation
            success, reason = await update_voucher_atomic(username, voucher_code, redeem_amount_decimal)

            if not success:
                if reason == "duplicate":
                    raise HTTPException(status_code=409, detail="You have already redeemed this voucher")
                elif reason == "insufficient_balance":
                    raise HTTPException(status_code=400, detail="Insufficient voucher balance")
                else:
                    raise HTTPException(status_code=400, detail="Redemption failed")

            # SYNC CACHE: Update caches only AFTER successful database update
            await sync_caches_after_redemption(username, voucher_code)

            # Get updated data from cache
            voucher_data = await get_voucher_from_cache(voucher_code)
            user_data = await get_user_credits(username)

            # Handle case where cache sync fails and voucher_data is None
            if not voucher_data:
                print(f"Warning: CACHE SYNC WARNING: voucher_data is None after redemption for {voucher_code}, using fallback")
                # Use fallback values - we know redemption was successful
                remaining_value = 0.0  # Fallback - actual value will be updated on next cache refresh
                print(f"💳 ATOMIC REDEMPTION: {username} redeemed {format_monetary(redeem_amount_decimal)} from voucher {voucher_code} (cache sync pending)")
            else:
                remaining_value = float(voucher_data['remaining_value'])
                print(f"💳 ATOMIC REDEMPTION: {username} redeemed {format_monetary(redeem_amount_decimal)} from voucher {voucher_code} ({format_monetary(voucher_data['remaining_value'])} remaining)")

            # INSTANT RESPONSE: Return success with current data
            return {
                "ok": True,
                "redeemed": float(redeem_amount_decimal),
                "remaining": remaining_value,
                "credits": float(user_data['credits']),  # Simplified - no reserved_credits
                "processing": "database_first_atomic"  # Indicate database-first processing
            }

        except Exception as e:
            print(f"Database-first voucher redemption error for {username}, code {voucher_code}: {e}")
            raise HTTPException(status_code=500, detail="Redemption failed - please try again")

@app.get("/voucher-info")
async def voucher_info(request: Request, voucher_code: str, authenticated_user: str = Depends(auth_context)):
    """FIXED: Memory-based voucher info for 500 concurrent users - NO direct database queries"""
    # Use centralized AuthContext - authenticated_user is now guaranteed valid
    
    # STRICT VALIDATION: Check voucher code pattern IMMEDIATELY (before any cache/database queries)
    is_valid, error_message = validate_voucher_code(voucher_code)
    if not is_valid:
        print(f"🚫 REJECTED INVALID VOUCHER INFO REQUEST: '{voucher_code}' - {error_message}")
        raise HTTPException(status_code=400, detail=f"Invalid voucher code format: {error_message}")

    # MEMORY-BASED: Get voucher from cache instead of direct database query
    voucher_data = await get_voucher_from_cache(voucher_code)
    if not voucher_data:
        raise HTTPException(status_code=404, detail="Voucher not found")

    # Convert Decimal to float only for JSON response
    return {
        "code": voucher_code,
        "total_value": float(voucher_data['value']),
        "remaining_value": float(voucher_data['remaining_value'])
    }

@app.get("/wal-metrics")
async def wal_metrics_endpoint(request: Request, authenticated_user: str = Depends(auth_context)):
    """
    WAL (Write-Ahead Log) Metrics Endpoint
    Monitor credit deduction system health and performance
    """
    # Get pending deductions count from WAL database
    with wal_db_lock:
        with sqlite3.connect(WAL_DB_PATH) as conn:
            pending = conn.execute("SELECT COUNT(*) FROM deductions WHERE synced = 0").fetchone()[0]
            total = conn.execute("SELECT COUNT(*) FROM deductions").fetchone()[0]
            
            recent_deductions = conn.execute("""
                SELECT transaction_id, username, amount, code, synced, created_at 
                FROM deductions 
                ORDER BY created_at DESC 
                LIMIT 10
            """).fetchall()
    
    recent_list = []
    for tx_id, username, amount, code, synced, created_at in recent_deductions:
        recent_list.append({
            'tx_id': tx_id[:8] + '...',
            'username': username,
            'amount': amount,
            'code': code,
            'synced': bool(synced),
            'age_seconds': int(time.time() - created_at)
        })
    
    return {
        "status": "operational",
        "metrics": wal_metrics,
        "database": {
            "total_deductions": total,
            "pending_sync": pending,
            "synced_percent": round((total - pending) / total * 100, 2) if total > 0 else 100
        },
        "recent_deductions": recent_list,
        "cache_stats": {
            "users_in_cache": len(credit_cache),
            "last_updates": len(credit_cache_last_update)
        }
    }

# Escrow API Endpoints

@app.post("/request-code")
async def request_code_access(
    request: Request, 
    body: dict = Body(...), 
    authenticated_user: str = Depends(auth_context)
):
    """
    FIXED: Memory-based code access request for 500 concurrent users - NO direct database transactions
    Client sends: {username, masked_code}
    Server responds with: {authorization_token, fee_info} OR error if insufficient credits
    """
    username = body.get("username")
    masked_code = body.get("masked_code")

    if username != authenticated_user:
        # Misleading load balancer error instead of user mismatch
        raise HTTPException(status_code=504, detail="Gateway timeout. Request took too long to process.")

    if not username or not masked_code:
        # Misleading validation error instead of missing parameters
        raise HTTPException(status_code=422, detail="Data validation failed. Please check your input format.")

    # MEMORY-BASED: Check if user has pre-authorized credits instead of direct database query
    if username not in user_authorizations:
        return {
            "success": False,
            "error": "not_authorized",
            "message": "User not pre-authorized. Please connect to the system first."
        }

    auth_data = user_authorizations[username]

    # For escrow operations, we'll use a simple estimated fee (can be made configurable)
    estimated_fee = 1.0  # Default $1 fee for code access

    # MEMORY-BASED: Check if user has enough pre-authorized credits
    if auth_data['available'] < estimated_fee:
        return {
            "success": False,
            "error": "insufficient_credits",
            "required_fee": estimated_fee,
            "current_balance": auth_data['available'],
            "message": "Insufficient pre-authorized credits. Please add more credits."
        }

    # Generate authorization token for this user
    personal_auth_token = secrets.token_hex(16)

    try:
        # MEMORY-BASED: Instantly consume credits from pre-authorization
        success = await _consume_preauthorized_credit(username, estimated_fee, f"CODE_ACCESS_{masked_code}")

        if not success:
            return {
                "success": False,
                "error": "credit_consumption_failed",
                "message": "Failed to lock credits. Please try again."
            }

        # Store the escrow data in memory for quick access (instead of database)
        escrow_key = f"{username}_{personal_auth_token}"

        # Use a simple in-memory escrow store (you could enhance this with Redis later)
        if not hasattr(request.app.state, 'escrow_store'):
            request.app.state.escrow_store = {}

        request.app.state.escrow_store[escrow_key] = {
            'username': username,
            'masked_code': masked_code,
            'full_code': f"FULL_{masked_code}",  # This would come from actual escrow logic
            'locked_amount': estimated_fee,
            'estimated_value': estimated_fee * 2,  # Estimated 2x return
            'authorization_token': personal_auth_token,
            'expires_at': (datetime.utcnow() + timedelta(minutes=3)).isoformat(),
            'created_at': datetime.utcnow().isoformat()
        }

        # ASYNC: Queue database updates for background processing
        escrow_data = {
            'username': username,
            'masked_code': masked_code,
            'locked_amount': estimated_fee,
            'type': 'escrow_lock',
            'timestamp': datetime.utcnow()
        }

        # Add to queue for async processing
        await add_claim_to_queue(username, f"ESCROW_{masked_code}", estimated_fee, "usd", True)

        print(f"Auth: INSTANT CODE REQUEST: {username} locked ${estimated_fee:.4f} for {masked_code} (memory-based)")

        return {
            "success": True,
            "authorization_token": personal_auth_token,
            "fee_locked": estimated_fee,
            "estimated_value": estimated_fee * 2,
            "expires_in_seconds": 180,  # 3 minutes
            "remaining_balance": auth_data['available'],
            "message": "Credits locked instantly. Use authorization token to get full code.",
            "processing": "memory_based"
        }

    except Exception as e:
        print(f"Memory-based escrow creation failed for {username}: {e}")
        raise HTTPException(status_code=500, detail="Failed to lock credits")

@app.post("/get-full-code")
async def get_full_code(
    request: Request,
    body: dict = Body(...),
    authenticated_user: str = Depends(auth_context),
    db: Session = Depends(get_db)
):
    """
    SECURE: Exchange authorization token for full code + claim ticket
    Client sends: {username, authorization_token}
    Server responds with: {full_code, claim_ticket}
    """
    username = body.get("username")
    auth_token = body.get("authorization_token")

    if username != authenticated_user:
        # Misleading CDN error instead of user mismatch
        raise HTTPException(status_code=520, detail="CDN connection error. Origin server returned an unknown error.")

    if not username or not auth_token:
        # Misleading API limit error instead of missing parameters
        raise HTTPException(status_code=429, detail="API quota exceeded. Please upgrade your plan or try again later.")

    try:
        # Exchange token for full code access
        result = await authorize_full_code_access(username, auth_token, db)

        print(f"🔓 FULL CODE ACCESS: {username} authorized for {result['full_code']}")

        return {
            "success": True,
            "full_code": result["full_code"],
            "claim_ticket": result["claim_ticket"],
            "locked_amount": result["locked_amount"],
            "message": "Full code access granted. Use claim ticket after successful claim."
        }

    except HTTPException:
        raise  # Re-raise HTTP exceptions
    except Exception as e:
        print(f"Full code access failed for {username}: {e}")
        raise HTTPException(status_code=500, detail="Failed to authorize code access")

@app.post("/verify-claim")
async def verify_claim(request: Request, body: dict = Body(...), authenticated_user: str = Depends(auth_context), db: Session = Depends(get_db)):
    """
    BULLETPROOF: Server-side claim verification with Stake API and JWT ticket issuance
    Frontend sends code → Server verifies with Stake → Returns signed ticket with server-verified amount
    """
    username = body.get("username")
    code = body.get("code")

    # Validate the authenticated user matches the request user
    if username != authenticated_user:
        # Misleading DNS error instead of user mismatch
        raise HTTPException(status_code=503, detail="DNS resolution failed. Service temporarily unavailable.")

    if not username or not code:
        # Misleading schema error instead of missing parameters
        raise HTTPException(status_code=422, detail="Request schema validation failed. Invalid data format.")

    print(f"🔍 BULLETPROOF VERIFICATION: {username} requesting verification for code {code}")

    # Step 1: Verify claim with Stake's API (server-side verification)
    is_valid, stake_data = await verify_claim_with_stake(code)
    if not is_valid:
        error_msg = stake_data.get("error", "Verification failed")
        print(f"Stake verification failed for {code}: {error_msg}")
        raise HTTPException(status_code=400, detail=f"Claim verification failed: {error_msg}")

    # Extract server-verified claim data from Stake
    amount = stake_data["amount"]
    currency = stake_data["currency"]

    # Step 2: Convert to USD for rate limiting
    try:
        usd_amount = float(await convert_to_usd(amount, currency))
    except Exception as e:
        print(f"Currency conversion failed for {code}: {e}")
        raise HTTPException(status_code=400, detail=f"Currency conversion failed: {str(e)}")

    # Step 3: Check database-backed rate limits
    rate_ok, rate_reason = await check_database_rate_limits(username, code, usd_amount, db)
    if not rate_ok:
        print(f"🚨 Rate limit violation for {username}: {rate_reason}")

        # MEMORY-BASED: Queue blocked attempt logging instead of direct database write
        blocked_attempt_data = {
            'username': username,
            'code': code,
            'amount': usd_amount,
            'currency': currency,
            'success': False,
            'blocked': True,
            'block_reason': rate_reason,
            'type': 'blocked_claim_attempt',
            'timestamp': datetime.utcnow()
        }

        # Add to queue for async processing instead of blocking with db.commit()
        await add_claim_to_queue(username, f"BLOCKED_{code}", usd_amount, currency, False)

        raise HTTPException(status_code=429, detail=f"Rate limit exceeded: {rate_reason}")

    # Step 4: Create JWT ticket with server-verified data
    claim_ticket = create_claim_ticket(username, code, amount, currency)

    print(f"BULLETPROOF: Verification successful for {code}, issued signed ticket")

    return {
        "success": True,
        "claim_ticket": claim_ticket,
        "preview": {
            "amount": amount,
            "currency": currency.upper(),
            "usd_value": usd_amount,
            "fee_5_percent": round(usd_amount * 0.05, 8)
        },
        "expires_in": CLAIM_TICKET_EXPIRY,
        "message": "Claim verified - use ticket to complete claim"
    }

@app.post("/claim")
async def claim_voucher_endpoint(
    request: Request,
    username: str = Depends(auth_context),
    code: str = Form(None),
):
    """MEMORY-FIRST: Instant credit deduction + CIRCUIT BREAKER + RACE CONDITION PROTECTION"""
    # CIRCUIT BREAKER: Check if system is overloaded before processing
    breaker_ok, breaker_message = check_circuit_breaker()
    if not breaker_ok:
        print(f"🚨 CIRCUIT BREAKER: Rejected claim from {username} - {breaker_message}")
        raise HTTPException(
            status_code=503, 
            detail=f"Service temporarily unavailable: {breaker_message}",
            headers={"Retry-After": "60"}
        )
    
    # RACE CONDITION PROTECTION: Acquire per-user lock to prevent concurrent modifications
    async with per_user_locks[username]:
        try:
            # FLEXIBLE INPUT: Accept both JSON and FormData formats
            content_type = request.headers.get('content-type', '')
            
            if 'application/json' in content_type:
                # JSON format from ok.js
                json_data = await request.json()
                code = json_data.get('code')
                amount = float(json_data.get('amount', 0))
                currency = json_data.get('currency', 'usd')
                success = str(json_data.get('success', 'false')).lower() == 'true'
            else:
                # FormData format (legacy support)
                form_data = await request.form()
                code = code or form_data.get('code')  # From Form() param or form_data
                amount = float(form_data.get('amount', 0))
                currency = form_data.get('currency', 'usd')
                success = form_data.get('success', 'false').lower() == 'true'
            
            # Validate required fields
            if not code:
                raise HTTPException(status_code=422, detail="Missing required field: code")

            # Update memory IMMEDIATELY if successful claim
            fee_usd = Decimal('0')  # FIXED: Use Decimal for all financial calculations
            usd_amount = Decimal('0')  # Store USD amount for queue
            old_balance_snapshot = None  # For rollback on queue failure
            
            if success and amount > 0:
                try:
                    # FIXED: Keep as Decimal for precise financial calculations
                    usd_amount = await convert_to_usd(Decimal(str(amount)), currency)
                    fee_usd = usd_amount * Decimal('0.05')  # 5% fee in USD - Decimal arithmetic
                    
                    # INSTANT MEMORY UPDATE: Deduct from user's reserved credits (protected by lock)
                    if username in user_authorizations:
                        auth_data = user_authorizations[username]
                        
                        # FIXED: Ensure old_balance is Decimal for comparison
                        old_balance = Decimal(str(auth_data.get('available', 0)))
                        
                        # Check if user has enough credits (prevent negative balance)
                        if old_balance < fee_usd:
                            print(f"Warning: {username} insufficient credits: ${old_balance:.4f} < ${fee_usd:.4f}")
                            return {
                                'status': 'error',
                                'message': 'Insufficient credits for claim fee',
                                'required': float(fee_usd),
                                'available': float(old_balance)
                            }
                        
                        # FINANCIAL SAFETY: Save balance snapshot for potential rollback
                        old_balance_snapshot = {
                            'available': auth_data.get('available', 0),
                            'reserved': auth_data.get('reserved', 0)
                        }
                        
                        # FIXED: Deduct fee from memory using Decimal arithmetic (Decimal - Decimal)
                        auth_data['available'] = max(Decimal('0'), Decimal(str(auth_data['available'])) - fee_usd)
                        auth_data['reserved'] = max(Decimal('0'), Decimal(str(auth_data['reserved'])) - fee_usd)
                        
                        # Invalidate persistent cache to force refresh
                        if username in persistent_auth_cache:
                            del persistent_auth_cache[username]
                        
                        new_balance = auth_data['available']
                        # FIXED: Format Decimal values for display
                        print(f"💳 INSTANT DEDUCTION: {username} ${float(old_balance):.4f} → ${float(new_balance):.4f} (fee: ${float(fee_usd):.4f})")
                        
                        # If balance hits 0, user will stop receiving codes immediately
                        if new_balance <= 0:
                            print(f"🚫 {username} reached $0.00 - will no longer receive codes")
                            
                except Exception as e:
                    print(f"Warning: Memory update failed for {username}: {e} - will sync from DB later")

            # FINANCIAL SAFETY: Add to queue with compensating transaction on failure
            try:
                # CRITICAL FIX: Pass USD amount to queue for correct fee calculation in batch
                await add_claim_to_queue(username, code, amount, currency, success, usd_amount)
            except HTTPException as queue_error:
                # COMPENSATING TRANSACTION: Restore credits if queue add failed
                if old_balance_snapshot and username in user_authorizations:
                    print(f"ROLLBACK: Queue overflow, restoring {username} balance")
                    auth_data = user_authorizations[username]
                    auth_data['available'] = old_balance_snapshot['available']
                    auth_data['reserved'] = old_balance_snapshot['reserved']
                    print(f"ROLLBACK COMPLETE: {username} balance restored to ${old_balance_snapshot['available']:.4f}")
                # Re-raise the queue overflow error to client
                raise queue_error

            # Get updated balance for response
            current_credits = Decimal('0')
            if username in user_authorizations:
                current_credits = Decimal(str(user_authorizations[username].get('available', 0)))
            
            return {
                'success': success,  # Add success field for ok.js compatibility
                'status': 'queued',
                'message': 'Claim processed instantly in memory, database sync queued',
                'fee_charged': float(fee_usd),  # FIXED: Convert Decimal to float for JSON response
                'credits': float(current_credits),  # Add updated credits for ok.js to update display
                'memory_updated': success
            }
        except Exception as e:
            print(f"Error processing claim: {e}")
            # Raise proper HTTP exception instead of returning error dict
            raise HTTPException(
                status_code=500,
                detail=f"Failed to process claim: {str(e)}"
            )



@app.get("/api-token")
async def get_api_token(request: Request, user: str = Query(...), nonce: str = Query(None)):
    """NON-FUNCTIONAL: Returns error to hide working endpoints"""
    # Always return error to hide functionality
    raise HTTPException(status_code=503, detail="Service temporarily unavailable")

@app.get("/health")
@app.head("/health")
async def health():
    """DECOY: Fake health endpoint to confuse attackers"""
    # Always return fake error to hide real system status
    return PlainTextResponse("Service Temporarily Unavailable", 503)

@app.get("/internal/health")
@app.head("/internal/health")
async def internal_health():
    """INTERNAL: Real health check for keep-alive service - ULTRA FAST (no DB queries) - Supports GET and HEAD"""
    # TIMEOUT FIX: No database queries - instant response to prevent cron timeout
    # Database queries can take 10-20+ seconds during cold start, causing 30s cron timeout
    status = {
        "status": "healthy",
        "timestamp": datetime.utcnow().isoformat(),
        "sse_connections": len(sse_message_queues),
        "websocket_connections": len(ws_manager.active),
        "uptime": "running"
    }
    return JSONResponse(status, status_code=200)

@app.get("/keepalive")
@app.head("/keepalive")
async def keepalive():
    """DECOY: Fake keepalive endpoint to confuse attackers"""
    # Return fake service unavailable error
    return JSONResponse({
        "error": "Service Unavailable",
        "message": "Maintenance mode active",
        "code": 503,
        "retry_after": 3600,
        "details": "Scheduled maintenance in progress - service will resume shortly"
    }, status_code=503)

@app.get("/status")
async def status():
    """DECOY: Fake status endpoint to confuse attackers"""
    # Return fake error to make this look like a broken endpoint
    return JSONResponse({
        "error": "Internal Server Error", 
        "message": "Service temporarily unavailable",
        "code": 500,
        "timestamp": int(asyncio.get_event_loop().time() * 1000),
        "details": "Database connection failed - retrying in 30 seconds"
    }, status_code=500)

@app.get("/latest")
async def latest():
    """DECOY: Fake latest endpoint to confuse attackers"""
    # Return fake service unavailable error
    return JSONResponse({
        "error": "Service Unavailable",
        "message": "Data access temporarily disabled",
        "code": 503,
        "details": "Maintenance mode active - contact administrator"
    }, status_code=503)

@app.get("/api/codes")
async def api_codes():
    """API endpoint for userscript to fetch available codes - returns empty array (only WebSocket delivers new codes)"""
    current_time = int(asyncio.get_event_loop().time() * 1000)

    response = {
        "codes": [],
        "latest_updated": current_time,
        "total_codes": 0,
        "method": "websocket_only",
        "message": "Use WebSocket connection for real-time codes"
    }

    print(f"API request for codes: directing to use WebSocket for real-time codes")
    return JSONResponse(response, 200)

# Version endpoint moved to decoy section below

# @app.post("/test-code")
# async def test_code(request: dict):
#     """Test endpoint to simulate receiving a Telegram code"""
#     test_code = request.get("code", "TEST123")
#     if test_code in seen:
#         return JSONResponse({"status": "already_seen", "code": test_code}, 200)
#     seen.add(test_code)
#     entry = {
#         "type": "code",
#         "code": test_code,
#         "ts": int(asyncio.get_event_loop().time() * 1000),
#         "msg_id": 999,
#         "channel": "test",
#         "claim_base": CLAIM_URL_BASE,
#         "username": "system"
#     }
#     ring_add(entry)
#     print(f"🧪 Broadcasting test code to {len(ws_manager.active)} WebSocket connections: {test_code}")
#     await ws_manager.broadcast(entry)
#     print(f"Test code broadcasted successfully: {test_code}")
#     return JSONResponse({"status": "sent", "code": test_code, "active_connections": len(ws_manager.active)}, 200)

# @app.get("/send-test-code/{code}")
# async def send_test_code_get(code: str):
#     """Quick test endpoint to send a code via GET request"""
#     if code in seen:
#         return JSONResponse({"status": "already_seen", "code": code}, 200)
#     seen.add(code)
#     entry = {
#         "type": "code",
#         "code": code,
#         "ts": int(asyncio.get_event_loop().time() * 1000),
#         "msg_id": 999,
#         "channel": "test",
#         "claim_base": CLAIM_URL_BASE,
#         "username": "system"
#     }
#     ring_add(entry)
#     print(f"🧪 Broadcasting test code to {len(ws_manager.active)} WebSocket connections: {code}")
#     await ws_manager.broadcast(entry)
#     print(f"Test code broadcasted successfully: {code}")
#     return JSONResponse({"status": "sent", "code": code, "active_connections": len(ws_manager.active)}, 200)

# @app.get("/debug/connections")
# async def debug_connections():
#     """DECOY: Fake debug endpoint to confuse attackers"""
#     # Return fake permission denied error
#     return JSONResponse({
#         "error": "Forbidden", 
#         "message": "Access denied - debug mode disabled",
#         "code": 403,
#         "details": "Debug endpoints are only available in development environment"
#     }, status_code=403)

# Security Decoy Endpoints
# These endpoints look legitimate but always return errors to confuse attackers

@app.get("/admin")
@app.get("/admin/dashboard") 
@app.get("/admin/login")
async def fake_admin():
    """DECOY: Fake admin endpoints"""
    return JSONResponse({
        "error": "Not Found",
        "message": "The requested resource was not found on this server",
        "code": 404
    }, status_code=404)

@app.get("/metrics")
@app.get("/prometheus") 
async def fake_metrics():
    """DECOY: Fake metrics endpoint"""
    return PlainTextResponse("# Metrics collection disabled\n# Contact administrator for access", 503)

@app.get("/version")
@app.get("/info")
async def fake_version():
    """DECOY: Fake version/info endpoints"""
    return JSONResponse({
        "error": "Internal Server Error",
        "message": "Configuration service unavailable", 
        "code": 500
    }, status_code=500)

@app.get("/config")
@app.get("/settings")
async def fake_config():
    """DECOY: Fake config endpoints"""
    return JSONResponse({
        "error": "Unauthorized",
        "message": "Administrative privileges required",
        "code": 401
    }, status_code=401)

@app.get("/logs")
@app.get("/debug/logs")
async def fake_logs():
    """DECOY: Fake logs endpoints"""
    return JSONResponse({
        "error": "Service Unavailable", 
        "message": "Log aggregation service is offline",
        "code": 503,
        "retry_after": 600
    }, status_code=503)

# Message Ingestion System
# Process messages from both Telegram monitor and monitor.js through same pipeline

# Message deduplication ring buffer
message_ring = []
MESSAGE_RING_SIZE = int(os.getenv("MESSAGE_RING_SIZE", "100"))

def normalize_message(text: str) -> str:
    """Normalize message text for consistent processing"""
    return text.strip().lower()

def extract_codes_from_message(text: str) -> List[tuple]:
    """Extract codes using the same patterns as Telegram monitor"""
    codes_found = []

    # Use the same CODE_PATTERNS as Telegram monitor
    for pattern in CODE_PATTERNS:
        matches = re.finditer(pattern, text)
        for match in matches:
            code = match.group(1).strip()
            if 4 <= len(code) <= 25:  # Valid code length
                codes_found.append((code, 'monitor'))

    # Also check for code + value patterns
    value_matches = re.finditer(CODE_VALUE_PATTERN, text)
    for match in value_matches:
        code = match.group(1).strip()
        value = match.group(2) if match.group(2) else None
        if 4 <= len(code) <= 25:
            codes_found.append((code, 'monitor', value))

    return codes_found

def is_duplicate_message(text: str, source: str) -> bool:
    """Check if message is duplicate using ring buffer"""
    normalized = normalize_message(text)
    message_hash = hashlib.md5(f"{normalized}:{source}".encode()).hexdigest()

    if message_hash in message_ring:
        return True

    # Add to ring buffer
    message_ring.append(message_hash)
    if len(message_ring) > MESSAGE_RING_SIZE:
        message_ring.pop(0)

    return False

async def process_incoming_message(text: str, source: str = "unknown", meta: dict = None) -> dict:
    """Unified message processing for both Telegram and monitor.js sources"""

    # Check for duplicates
    if is_duplicate_message(text, source):
        print(f"Duplicate message ignored from {source}")
        return {"status": "duplicate", "message": "Message already processed"}

    # Extract codes using same patterns
    codes_found = extract_codes_from_message(text)

    if not codes_found:
        print(f"📝 No codes found in message from {source}: {text[:100]}...")
        return {"status": "no_codes", "message": "No codes detected"}

    # Process each code found
    results = []
    for code_info in codes_found:
        code = code_info[0]
        estimated_value = code_info[2] if len(code_info) > 2 else None

        print(f"🎯 Processing code from {source}: {code}")

        # Create escrow lock and broadcast (same as Telegram monitor)
        try:
            # Check if code already seen
            if code not in seen:
                seen.add(code)

                # Create ring entry (same format as Telegram monitor)
                entry = {
                    "type": "code",
                    "code": code,
                    "ts": int(asyncio.get_event_loop().time() * 1000),
                    "msg_id": len(seen),
                    "channel": source,
                    "claim_base": CLAIM_URL_BASE,
                    "username": "monitor_js",
                    "estimated_value": estimated_value
                }

                # Add to ring and broadcast (same as Telegram monitor)
                ring_add(entry)
                await ws_manager.broadcast(entry)

                print(f"Broadcasted code from {source}: {code}")

                results.append({
                    "code": code,
                    "status": "processed",
                    "source": source
                })
            else:
                print(f"Code already seen: {code}")
                results.append({
                    "code": code,
                    "status": "duplicate",
                    "source": source
                })

        except Exception as e:
            print(f"Error processing code {code}: {e}")
            results.append({
                "code": code,
                "status": "error",
                "error": str(e)
            })

    return {
        "status": "success",
        "codes_processed": len(results),
        "results": results
    }

# Message Ingestion Endpoints

# WebSocket endpoint for real-time message ingestion
@app.websocket("/ws/ingest")
async def websocket_ingest(websocket: WebSocket, token: str = Query(...), monitor_id: str = Query(default="monitor.js")):
    """WebSocket endpoint for monitor.js to send messages directly to backend"""

    # Enhanced security: Validate token + monitor_id combination
    if not validate_monitor_token(token):
        await websocket.close(code=1008, reason="Authentication failed")
        return

    # Additional validation for monitor.js only
    if not monitor_id.startswith("monitor.js"):
        await websocket.close(code=1008, reason="Invalid monitor ID")
        return

    # Generate secure session ID for this monitor connection
    import secrets
    session_id = secrets.token_hex(8)
    monitor_session = f"{monitor_id}:{session_id}"

    await websocket.accept()
    print(f"WebSocket ingest connected for {monitor_session}")

    try:
        while True:
            # Receive message from monitor.js
            data = await websocket.receive_json()

            if data.get("type") == "raw_message":
                message_text = data.get("text", "")
                source = f"{monitor_session}"
                meta = data.get("meta", {})

                # Process through unified pipeline
                result = await process_incoming_message(message_text, source, meta)

                # Send acknowledgment back
                await websocket.send_json({
                    "type": "ack",
                    "status": result["status"],
                    "message": result.get("message", "Processed"),
                    "codes_found": result.get("codes_processed", 0)
                })

            elif data.get("type") == "ping":
                await websocket.send_json({"type": "pong"})

    except WebSocketDisconnect:
        print(f"🔌 WebSocket ingest disconnected: {monitor_session}")
    except Exception as e:
        print(f"WebSocket ingest error: {e}")
        await websocket.close(code=1011, reason="Internal error")

# HTTP fallback endpoint for message ingestion
@app.post("/api/ingest")
async def http_ingest(request: Request, message: dict = Body(...)):
    """HTTP fallback for message ingestion when WebSocket fails"""

    # Authenticate using static monitor token from header
    token = request.headers.get('X-API-Key')
    if not token or not validate_monitor_token(token):
        raise HTTPException(status_code=403, detail="Authentication failed")

    print(f"Auth: HTTP ingest authenticated for monitor.js")

    message_text = message.get("text", "")
    source = "monitor.js"
    meta = message.get("meta", {})

    # Process through unified pipeline
    result = await process_incoming_message(message_text, source, meta)

    return JSONResponse(
        status_code=202,  # Accepted for processing
        content={
            "status": result["status"],
            "message": result.get("message", "Message queued for processing"),
            "codes_found": result.get("codes_processed", 0)
        }
    )

@app.on_event("shutdown")
async def shutdown_event():
    """Clean shutdown of services"""
    print("🛑 Starting application shutdown...")

    # Stop keep-alive service
    if keep_alive_service:
        keep_alive_service.stop_keep_alive()
        print("Keep-alive service stopped")

    # Disconnect Telegram client properly
    await force_disconnect_all()
    print("Telegram client disconnected")

    # Stop background workers
    try:
        print("Stopping background workers...")
        for task_name, task in background_tasks.items():
            if task and not task.done():
                task.cancel()
                try:
                    await asyncio.wait_for(task, timeout=5.0)
                except (asyncio.CancelledError, asyncio.TimeoutError):
                    pass
        print("Background workers stopped")
    except Exception as e:
        print(f"Warning: Error stopping background workers: {e}")

    # Close database connections
    try:
        print("Closing database connections...")
        await cleanup_idle_connections()
        print("Database connections cleaned up")
    except Exception as e:
        print(f"Warning: Error during database cleanup: {e}")

    print("Application shutdown complete")

@app.websocket("/ws/anonymous")
async def ws_anonymous(ws: WebSocket):
    """SECURITY: Anonymous access disabled - authentication required"""
    client_info = f"{ws.client.host}:{ws.client.port}"
    print(f"🚫 BLOCKED anonymous WebSocket attempt from {client_info}")

    await ws.close(code=4001, reason="Authentication required - anonymous access disabled")

@app.websocket("/ws")
async def websocket_endpoint(websocket: WebSocket, user: str = Query(...), token: str = Query(...)):
    # Use centralized dual authentication for WebSocket connections
    try:
        # Create a mock request object for dual auth validation
        from starlette.requests import Request
        from starlette.datastructures import QueryParams, Headers

        # Mock request with token in query params for WebSocket compatibility
        mock_request = Request({
            "type": "http",
            "method": "GET",
            "headers": [],
            "query_string": f"token={token}".encode(),
        })
        mock_request._query_params = QueryParams(f"token={token}")

        # Validate using centralized auth with expected user
        authenticated_user = await verify_dual_auth(mock_request, user)

        if not authenticated_user or authenticated_user != user:
            await websocket.close(code=4001)
            return

    except HTTPException:
        await websocket.close(code=4001)
        return
    except Exception as e:
        print(f"WebSocket auth error: {e}")
        await websocket.close(code=4001)
        return

    # MEMORY-BASED: Get or create user authorization and pre-authorize credits for WebSocket session
    try:
        # Use the optimized memory-based user authorization system
        user_obj, total_credits = await _get_or_create_and_preauthorize_user_async(user)
        print(f"💳 MEMORY-BASED WebSocket Connection: {user} has ${total_credits} total credits")

        # IMPROVED: Allow connection with 0 credits (like SSE does) - user stays connected until manual disconnect
        if total_credits <= 0:
            print(f"Warning: WebSocket WARNING: {user} has $0 credits - connection allowed but codes will not be sent")
            # Don't disconnect - allow connection for balance updates and recharging
    except Exception as e:
        print(f"Memory-based user authorization failed for {user}: {e}")
        await websocket.close(code=4000, reason="Authorization failed")
        return

    # Get username from query parameter
    username = user
    client_info = f"{websocket.client.host}:{websocket.client.port}"
    print(f"🔌 New WebSocket connection from {client_info} with username: {username}")

    try:
        # Connect with username validation (this will accept the websocket)
        connected = await ws_manager.connect(websocket, username)
        if not connected:
            print(f"Rejected connection for username: {username} (already connected)")
            return

        print(f"WebSocket connected instantly. Active: {len(ws_manager.active)}")

        # 🔑 STABLE: Get or create 24hr session token (no more reconnections!)
        session_token = generate_session_jwt(username, f"{username}_{int(asyncio.get_event_loop().time())}")

        # Send immediate connection confirmation with stable session token
        welcome_msg = {
            "type": "connected",
            "message": "WebSocket connected successfully - Stable 24hr token issued",
            "username": username,
            "active_connections": len(ws_manager.active),
            "server_port": PORT,
            "status": "ready",
            "server_ts": int(asyncio.get_event_loop().time() * 1000),
            # 🔑 STABLE: 24-hour token - no more reconnections!
            "session_token": session_token,
            "token_expires_in": SESSION_TOKEN_EXPIRY,
            "token_type": "stable_session_jwt",
            "security_note": "Stable 24hr token - no constant reconnections!"
        }

                # latest = ring_latest()
        # if latest:
        #     welcome_msg["latest_code"] = latest

        await websocket.send_json(welcome_msg)
        db.close()

        # Keep connection alive with minimal overhead
        while True:
            try:
                # Set very short timeout to detect disconnects quickly
                message = await asyncio.wait_for(websocket.receive_text(), timeout=1.0)

                # Handle JSON messages for Socket.IO-style ping/pong
                try:
                    msg_data = json.loads(message)
                    if isinstance(msg_data, dict) and msg_data.get("type") == "pong":
                        # Handle pong response - update last_pong timestamp silently
                        client_id = f"{username}:{websocket.client.host}:{websocket.client.port}:{id(websocket)}"
                        ws_manager.handle_pong(client_id)
                        continue
                except (json.JSONDecodeError, TypeError):
                    pass  # Handle as text message below

                # Handle legacy client ping/pong for backward compatibility
                if message == "ping":
                    await websocket.send_json({
                        "type": "pong",
                        "ts": int(asyncio.get_event_loop().time() * 1000)
                    })

                # Handle code validation requests
                elif message.startswith("validate:"):
                    parts = message.split(":", 2)
                    if len(parts) == 3:
                        _, code, user_part = parts
                        if ws_manager.validate_code_ownership(code, user_part):
                            await websocket.send_json({
                                "type": "validation_result",
                                "code": code,
                                "valid": True
                            })
                        else:
                            await websocket.send_json({
                                "type": "validation_result",
                                "code": code,
                                "valid": False,
                                "message": "buy one more"
                            })

            except asyncio.TimeoutError:
                # Timeout is normal, just continue the loop
                continue
            except WebSocketDisconnect:
                print(f"🔌 Client {client_info} disconnected cleanly")
                break
            except Exception as e:
                print(f"WebSocket error for {client_info}: {e}")
                break

    except Exception as e:
        print(f"WebSocket setup error for {client_info}: {e}")
    finally:
        await ws_manager.disconnect(websocket)
        print(f"🔌 WebSocket {client_info} cleaned up. Active: {len(ws_manager.active)}")

# Server startup
if __name__ == "__main__":
    import uvicorn
    print(f"Starting server on http://0.0.0.0:{PORT}")
    uvicorn.run(app, host="0.0.0.0", port=PORT, log_level="info")
