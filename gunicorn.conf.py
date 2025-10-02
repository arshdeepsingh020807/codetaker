# Gunicorn configuration for VPS deployment - Production Optimized for 300+ Users
import os

# Server socket - Production configuration
bind = "0.0.0.0:5000"
backlog = 8192  # Increased backlog for high concurrent connections

# Worker processes - SINGLE WORKER ARCHITECTURE FOR STABLE SSE/WebSocket CONNECTIONS
workers = 1                                    # Single worker eliminates state coordination issues
worker_class = "uvicorn.workers.UvicornWorker" # ASGI server for FastAPI + WebSockets
worker_connections = 1000                      # Max concurrent connections per worker
timeout = 85                                   # Render-safe timeout (under 90s limit) with lifetime user connections
keepalive = 5                                  # Keep connections alive longer
graceful_timeout = 60                          # Faster shutdown for Render compatibility

# Worker lifecycle management - Optimized for production stability
max_requests = 5000                            # Restart after more requests (production stable)
max_requests_jitter = 500                      # Jitter to prevent thundering herd
worker_tmp_dir = "/dev/shm"                     # Use shared memory for better performance

# Logging - Production level
accesslog = "/var/log/creditsystem/access.log"
errorlog = "/var/log/creditsystem/error.log"
loglevel = "warning"                           # Reduced logging for production performance
capture_output = True
enable_stdio_inheritance = True
access_log_format = '%(t)s [%(p)s] %(h)s "%(r)s" %(s)s %(b)s "%(f)s" "%(a)s" %(D)s'

# Process naming
proc_name = 'creditsystem-production'

# Production daemon settings
daemon = False                                 # Systemd will handle daemonization
pidfile = "/var/run/creditsystem.pid"
user = "creditsystem"                          # Run as dedicated user
group = "creditsystem"                         # Run as dedicated group

# Performance optimizations
preload_app = True                             # Preload for better memory usage
sendfile = True                                # Use sendfile for static files
reuse_port = True                              # SO_REUSEPORT for better load distribution

# Security settings
limit_request_line = 8192                      # Limit request line size
limit_request_fields = 200                     # Limit number of headers
limit_request_field_size = 16384               # Limit header size

# Environment-specific settings
if os.getenv('ENVIRONMENT') == 'development':
    reload = True
    loglevel = "debug"
else:
    reload = False
    
# Memory and performance tuning for 300+ users
worker_memory_limit = 1024 * 1024 * 1024       # 1GB memory limit per worker
max_worker_memory = 1024 * 1024 * 1024         # 1GB max memory before restart

# Single worker architecture - No post_fork hook needed
# All state is maintained in-memory within the single worker process
# This eliminates the need for Redis or other external state coordination

def when_ready(server):
    """Called when the server is ready to accept connections"""
    server.log.info("🚀 Credit System Production Server Ready")
    server.log.info("🌐 Domain: kciade.online")
    server.log.info("👥 Capacity: 300+ concurrent users")
    server.log.info("🗃️ Database: Supabase PostgreSQL")
    server.log.info("⚡ Architecture: Single Worker + In-Memory State")

def worker_int(worker):
    """Called when a worker receives the INT or QUIT signal"""
    worker.log.info("Worker received INT/QUIT signal - graceful shutdown")

# SSL handled by Nginx reverse proxy
# No SSL configuration needed at Gunicorn level
