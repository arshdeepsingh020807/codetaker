
import asyncio
import aiohttp
import logging
from datetime import datetime

logger = logging.getLogger(__name__)

class KeepAliveService:
    def __init__(self, url: str, interval_minutes: int = 5):
        self.url = url
        self.interval_seconds = interval_minutes * 60
        self.is_running = False

    async def ping_self(self):
        """Ping the service to keep it alive with retry logic"""
        # TIMEOUT FIX: Reduce timeout to 15s and add retries for cold start reliability
        max_retries = 2
        timeout_seconds = 15
        
        for attempt in range(max_retries):
            try:
                async with aiohttp.ClientSession() as session:
                    async with session.get(
                        f"{self.url}/internal/health", 
                        timeout=aiohttp.ClientTimeout(total=timeout_seconds)
                    ) as response:
                        if response.status == 200:
                            logger.info(f"✅ Keep-alive ping successful at {datetime.now()}")
                            return True
                        else:
                            logger.warning(f"⚠️ Keep-alive ping returned status {response.status}")
                            if attempt < max_retries - 1:
                                await asyncio.sleep(2)  # Wait 2s before retry
                                continue
                            return False
            except asyncio.TimeoutError:
                logger.warning(f"⏰ Keep-alive ping timeout (attempt {attempt + 1}/{max_retries})")
                if attempt < max_retries - 1:
                    await asyncio.sleep(2)  # Wait 2s before retry
                    continue
                return False
            except Exception as e:
                logger.error(f"❌ Keep-alive ping failed (attempt {attempt + 1}/{max_retries}): {e}")
                if attempt < max_retries - 1:
                    await asyncio.sleep(2)  # Wait 2s before retry
                    continue
                return False
        
        return False

    async def start_keep_alive(self):
        """Start the keep-alive loop"""
        if self.is_running:
            return

        self.is_running = True
        logger.info(f"🚀 Starting keep-alive service (ping every {self.interval_seconds/60} minutes)")

        while self.is_running:
            try:
                await self.ping_self()
                await asyncio.sleep(self.interval_seconds)
            except Exception as e:
                logger.error(f"❌ Keep-alive service error: {e}")
                await asyncio.sleep(60)  # Wait 1 minute before retrying

    def stop_keep_alive(self):
        """Stop the keep-alive service"""
        self.is_running = False
        logger.info("🛑 Keep-alive service stopped")
