"""Compatibility imports for the pre-service declaration-checking module.

Declaration orchestration now lives in :mod:`py_nanobruijn.services.checker`.
This module intentionally has no import-time side effects.
"""

from .services.checker import CheckerService

__all__ = ["CheckerService"]
