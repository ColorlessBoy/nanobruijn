from __future__ import annotations

import pytest

from .config import Config
from .parser import parse_export_file


def test_parse_and_check_all_resources():
    """Parse and try checking all test resources."""
    import os
    resources = [
        "test_resources/Empty",
        "test_resources/SparseNameIndex",
        "test_resources/LevelIndexOutOfOrder",
    ]
    for res in resources:
        config_path = f"{res}/config.json"
        if not os.path.exists(config_path):
            continue
        cf = Config.from_json(config_path)
        if cf.export_file_path and os.path.exists(cf.export_file_path):
            export = parse_export_file(cf.export_file_path, cf)
            panics = export.check_all_declars()
            assert panics == 0, f"{res} panicked"


def test_proj_from_prop_panics():
    """ProjFromProp should panic with infer_proj prop."""
    cf = Config.from_json("test_resources/ProjFromProp/config.json")
    cf.unsafe_permit_all_axioms = True
    assert cf.export_file_path is not None
    export = parse_export_file(cf.export_file_path, cf)
    with pytest.raises(Exception, match="infer_proj"):
        export.check_all_declars()
