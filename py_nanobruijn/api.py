"""Stable high-level API for loading and checking Lean exports."""
from __future__ import annotations

from .config import Config
from .parser import ExportFile, parse_export_file
from .results import CheckResult


def load_export(path: str, config: Config | None = None) -> ExportFile:
    """Parse an NDJSON Lean export from *path*."""
    return parse_export_file(path, config or Config(export_file_path=path))


def check_export(path: str, config: Config | None = None, *, keep_going: bool = False) -> CheckResult:
    """Load and check an export, returning a structured result."""
    return load_export(path, config).check_all(keep_going=keep_going)
