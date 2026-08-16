from __future__ import annotations

import os

from .config import Config
from .env import Axiom, Definition, InductiveDecl
from .name import name_to_string
from .parser import parse_export_file

TEST_ROOT = os.path.normpath(
    os.path.join(os.path.dirname(__file__), '..', 'test_resources')
)


def _config():
    return Config(
        nat_extension=True,
        string_extension=True,
        unsafe_permit_all_axioms=True,
    )


def test_empty():
    path = os.path.join(TEST_ROOT, 'Empty', 'export')
    ef = parse_export_file(path, _config())
    assert len(ef.declars) == 0
    print("test_empty: OK")


def test_sparse_name_index():
    path = os.path.join(TEST_ROOT, 'SparseNameIndex', 'export')
    ef = parse_export_file(path, _config())
    assert len(ef.declars) == 1
    name = list(ef.declars.keys())[0]
    decl = ef.declars[name]
    assert isinstance(decl, Axiom), f"expected Axiom, got {type(decl)}"
    name_str = name_to_string(ef.dag.get_name(name), ef.dag.names, ef.dag.strings)
    assert name_str == "foo", f"expected 'foo', got '{name_str}'"
    print("test_sparse_name_index: OK")


def test_level_index_out_of_order():
    path = os.path.join(TEST_ROOT, 'LevelIndexOutOfOrder', 'export')
    ef = parse_export_file(path, _config())
    assert len(ef.declars) == 1
    name = list(ef.declars.keys())[0]
    decl = ef.declars[name]
    assert isinstance(decl, Axiom), f"expected Axiom, got {type(decl)}"
    name_str = name_to_string(ef.dag.get_name(name), ef.dag.names, ef.dag.strings)
    assert name_str == "foo"
    print("test_level_index_out_of_order: OK")


def test_proj_from_prop():
    path = os.path.join(TEST_ROOT, 'ProjFromProp', 'export')
    ef = parse_export_file(path, _config())
    # Count declarations: axioms + defs + inductives + constructors + recursors
    num_axioms = sum(1 for d in ef.declars.values() if isinstance(d, Axiom))
    num_defs = sum(1 for d in ef.declars.values() if isinstance(d, Definition))
    num_inductives = sum(1 for d in ef.declars.values() if isinstance(d, InductiveDecl))
    num_inductive_blocks = num_inductives
    print(f"  decls: {len(ef.declars)} total, {num_axioms} axioms, {num_defs} defs, {num_inductive_blocks} inductive blocks")
    # Whole file: 2 inductives + 2 constructors + 2 recursors + 2 defs = 8
    assert len(ef.declars) == 8, f"expected 8 declarations, got {len(ef.declars)}"
    # Can look for specific names
    has_explosion = False
    has_explosion_helper = False
    for name, decl in ef.declars.items():
        s = name_to_string(ef.dag.get_name(name), ef.dag.names, ef.dag.strings)
        if s == "explosion":
            has_explosion = True
            assert isinstance(decl, Definition)
        if s == "explosion_helper":
            has_explosion_helper = True
            assert isinstance(decl, Definition)
    assert has_explosion, "missing 'explosion' definition"
    assert has_explosion_helper, "missing 'explosion_helper' definition"
    print("test_proj_from_prop: OK")


def test_parse_all_debug():
    """Parse all test files and report stats."""
    config = _config()
    for test_name in ['Empty', 'SparseNameIndex', 'LevelIndexOutOfOrder', 'ProjFromProp']:
        path = os.path.join(TEST_ROOT, test_name, 'export')
        ef = parse_export_file(path, config)
        print(f"{test_name}: {len(ef.declars)} decls, {len(ef.skipped)} skipped")


if __name__ == '__main__':
    test_empty()
    test_sparse_name_index()
    test_level_index_out_of_order()
    test_proj_from_prop()
    test_parse_all_debug()
    print("\nAll tests passed!")
