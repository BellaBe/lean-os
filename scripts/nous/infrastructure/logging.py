"""
Nous Logging - Structured file-based logging for debugging.

Logs are written to {project_dir}/logs/nous_YYYYMMDD_HHMMSS.log

Features:
- Project-local log directory (not ~/.nous)
- Silences noisy third-party loggers (httpcore, hpack, urllib3)
- Configurable log levels per component
- Clean, readable output format
"""

import logging
import os
import warnings
from datetime import datetime
from pathlib import Path
from typing import Literal

# Log level type
LogLevel = Literal["DEBUG", "INFO", "WARNING", "ERROR", "CRITICAL"]

# Noisy third-party loggers to silence
NOISY_LOGGERS = [
    "httpcore",
    "httpcore.http2",
    "httpcore.http11",
    "httpcore.connection",
    "hpack",
    "hpack.hpack",
    "hpack.table",
    "urllib3",
    "urllib3.connectionpool",
    "httpx",
    "httpx._client",
    "aiosqlite",
    "asyncio",
    "charset_normalizer",
    "filelock",
    "PIL",
    "h2",
    "h2.connection",
    "h2.stream",
]

# LiteLLM loggers to control (keep at INFO to see API calls, silence internal debug)
LITELLM_LOGGERS = [
    "LiteLLM",
    "litellm",
    "LiteLLM Proxy",
    "LiteLLM Router",
]


def _get_project_log_dir() -> Path:
    """
    Get the project-local log directory.

    Returns logs directory relative to the nous package root.
    """
    # Get the directory containing this file (infrastructure/)
    infrastructure_dir = Path(__file__).parent
    # Go up to nous/ package root
    package_root = infrastructure_dir.parent
    # Create logs directory in package root
    log_dir = package_root / "logs"
    return log_dir


def _silence_noisy_loggers(level: int = logging.WARNING) -> None:
    """
    Silence noisy third-party loggers.

    Sets httpcore, hpack, urllib3, and similar libraries to WARNING level
    to prevent them from flooding the logs with HTTP/2 wire traces.
    """
    for logger_name in NOISY_LOGGERS:
        logging.getLogger(logger_name).setLevel(level)


def _configure_litellm_logging(level: int = logging.INFO) -> None:
    """
    Configure LiteLLM logging.

    - Keeps INFO level for API call visibility
    - Suppresses the GenericAPILogger enterprise warning
    """
    for logger_name in LITELLM_LOGGERS:
        logging.getLogger(logger_name).setLevel(level)

    # Suppress the "Unable to import GenericAPILogger" warning
    warnings.filterwarnings(
        "ignore",
        message=".*GenericAPILogger.*",
        category=UserWarning,
    )
    warnings.filterwarnings(
        "ignore",
        message=".*LiteLLM Enterprise.*",
        category=UserWarning,
    )


def setup_logging(
    name: str = "nous",
    level: int = logging.DEBUG,
    silence_noisy: bool = True,
) -> logging.Logger:
    """
    Setup file-based logging for Nous.

    Args:
        name: Logger name
        level: Logging level for nous loggers
        silence_noisy: Whether to silence noisy third-party loggers

    Returns:
        Configured logger
    """
    # Create logs directory in project
    log_dir = _get_project_log_dir()
    log_dir.mkdir(parents=True, exist_ok=True)

    # Create log file with timestamp
    timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
    log_file = log_dir / f"nous_{timestamp}.log"

    # Configure logger
    logger = logging.getLogger(name)
    logger.setLevel(level)

    # Remove existing handlers
    logger.handlers = []

    # File handler - detailed logs
    file_handler = logging.FileHandler(log_file, encoding="utf-8")
    file_handler.setLevel(logging.DEBUG)
    file_format = logging.Formatter(
        "%(asctime)s | %(levelname)-8s | %(name)-30s | %(message)s",
        datefmt="%H:%M:%S"
    )
    file_handler.setFormatter(file_format)
    logger.addHandler(file_handler)

    # Console handler - errors only (to not clutter stdout)
    console_handler = logging.StreamHandler()
    console_handler.setLevel(logging.ERROR)
    console_format = logging.Formatter("%(levelname)s: %(message)s")
    console_handler.setFormatter(console_format)
    logger.addHandler(console_handler)

    # Silence noisy loggers
    if silence_noisy:
        _silence_noisy_loggers()
        _configure_litellm_logging()

    logger.info(f"Logging to: {log_file}")

    return logger


def get_logger(name: str = "nous") -> logging.Logger:
    """Get or create a logger."""
    logger = logging.getLogger(name)
    if not logger.handlers:
        return setup_logging(name)
    return logger


# Pre-configured loggers for different components
def get_search_logger() -> logging.Logger:
    return get_logger("nous.search")


def get_crawl_logger() -> logging.Logger:
    return get_logger("nous.crawl")


def get_extract_logger() -> logging.Logger:
    return get_logger("nous.extract")


def get_rate_logger() -> logging.Logger:
    return get_logger("nous.rate")


# Global log file path for reference
_current_log_file: Path | None = None


def get_current_log_file() -> Path | None:
    """Get the current log file path."""
    global _current_log_file
    return _current_log_file


def init_session_logging(
    app_level: LogLevel = "INFO", # Log level for nous application logs, can be DEBUG for more detail
    third_party_level: LogLevel = "WARNING",
    litellm_level: LogLevel = "INFO",
) -> Path:
    """
    Initialize logging for a new session.

    Args:
        app_level: Log level for nous application logs
        third_party_level: Log level for noisy third-party libraries
        litellm_level: Log level for LiteLLM (API calls)

    Returns:
        Path to the log file
    """
    global _current_log_file

    # Use project-local log directory
    log_dir = _get_project_log_dir()
    log_dir.mkdir(parents=True, exist_ok=True)

    timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
    log_file = log_dir / f"nous_{timestamp}.log"
    _current_log_file = log_file

    # Convert string levels to int
    app_level_int = getattr(logging, app_level)
    third_party_level_int = getattr(logging, third_party_level)
    litellm_level_int = getattr(logging, litellm_level)

    # Configure root logger with file output only
    # (prevents double-printing to console)
    root_logger = logging.getLogger()
    root_logger.setLevel(logging.DEBUG)

    # Remove any existing handlers on root
    root_logger.handlers = []

    # Add file handler to root
    file_handler = logging.FileHandler(log_file, encoding="utf-8")
    file_handler.setLevel(logging.DEBUG)
    file_format = logging.Formatter(
        "%(asctime)s | %(levelname)-8s | %(name)-30s | %(message)s",
        datefmt="%H:%M:%S"
    )
    file_handler.setFormatter(file_format)
    root_logger.addHandler(file_handler)

    # Silence noisy third-party loggers
    _silence_noisy_loggers(third_party_level_int)
    _configure_litellm_logging(litellm_level_int)

    # Configure nous logger
    nous_logger = logging.getLogger("nous")
    nous_logger.setLevel(app_level_int)

    # Log session start
    nous_logger.info("=" * 60)
    nous_logger.info("NOUS SESSION STARTED")
    nous_logger.info(f"Log file: {log_file}")
    nous_logger.info(f"Log levels: app={app_level}, third_party={third_party_level}, litellm={litellm_level}")
    nous_logger.info("=" * 60)

    return log_file


def cleanup_old_logs(max_files: int = 20) -> int:
    """
    Remove old log files, keeping only the most recent ones.

    Args:
        max_files: Maximum number of log files to keep

    Returns:
        Number of files removed
    """
    log_dir = _get_project_log_dir()
    if not log_dir.exists():
        return 0

    # Get all log files sorted by modification time (newest first)
    log_files = sorted(
        log_dir.glob("nous_*.log"),
        key=lambda p: p.stat().st_mtime,
        reverse=True
    )

    # Remove files beyond the limit
    removed = 0
    for log_file in log_files[max_files:]:
        try:
            log_file.unlink()
            removed += 1
        except OSError:
            pass

    return removed
