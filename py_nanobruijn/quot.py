from __future__ import annotations

from .env import QuotDecl


def check_quot_declaration(export, d: QuotDecl):
    """Verify a Quot declaration.

    For each QuotDecl, runs check_declar_info which:
    1. Verifies no duplicate universe parameters
    2. Verifies the type has no free variables
    3. Infers the type and checks it's a Sort
    """
    tc = export._with_tc(d)
    tc.check_declar_info(d)
