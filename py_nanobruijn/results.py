"""Structured, presentation-independent outcomes for checking operations."""
from __future__ import annotations

from dataclasses import asdict, dataclass, field
from typing import Any, Optional


@dataclass(frozen=True)
class Diagnostic:
    severity: str
    message: str
    declaration: Optional[str] = None
    declaration_index: Optional[int] = None
    exception_type: Optional[str] = None

    def to_dict(self) -> dict[str, Any]:
        return asdict(self)


@dataclass(frozen=True)
class CheckResult:
    checked: int
    failed: int
    skipped: int
    elapsed_ms: int
    diagnostics: tuple[Diagnostic, ...] = field(default_factory=tuple)

    @property
    def ok(self) -> bool:
        return self.failed == 0

    def to_dict(self) -> dict[str, Any]:
        data = asdict(self)
        data["ok"] = self.ok
        return data
