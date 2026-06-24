from __future__ import annotations

from .env import QuotDecl
from .parser import ExportFile


def check_quot(self: ExportFile, d: QuotDecl):
    """Verify a Quot declaration.

    For each QuotDecl, runs check_declar_info which:
    1. Verifies no duplicate universe parameters
    2. Verifies the type has no free variables
    3. Infers the type and checks it's a Sort
    """
    tc = self._with_tc(d)
    tc.check_declar_info(d)


ExportFile.check_quot = check_quot
