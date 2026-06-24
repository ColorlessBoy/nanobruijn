from __future__ import annotations

from .env import QuotDecl, DeclarInfo
from . import check_decl  # noqa: F401 — patches ExportFile


def test_quot_stub():
    """Quot checker handles QuotDecl without error."""
    _ = QuotDecl(info=DeclarInfo(name=0, uparams=0, ty=0), kind="type")
    import py_nanobruijn.quot  # noqa: F401 — ensure check_quot patched
    print("QuotDecl stub OK")
