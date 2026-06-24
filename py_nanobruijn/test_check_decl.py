from __future__ import annotations
import pytest

from .parser import parse_export_file
from .config import Config


def test_check_empty():
    cf = Config.from_json("test_resources/Empty/config.json")
    assert cf.export_file_path is not None
    export = parse_export_file(cf.export_file_path, cf)
    panics = export.check_all_declars()
    assert panics == 0


def test_check_sparse_name_index():
    cf = Config.from_json("test_resources/SparseNameIndex/config.json")
    cf.unsafe_permit_all_axioms = True
    assert cf.export_file_path is not None
    export = parse_export_file(cf.export_file_path, cf)
    panics = export.check_all_declars()
    assert panics == 0


def test_check_proj_from_prop():
    with pytest.raises(Exception, match="infer_proj"):
        cf = Config.from_json("test_resources/ProjFromProp/config.json")
        cf.unsafe_permit_all_axioms = True
        assert cf.export_file_path is not None
        export = parse_export_file(cf.export_file_path, cf)
        export.check_all_declars()
