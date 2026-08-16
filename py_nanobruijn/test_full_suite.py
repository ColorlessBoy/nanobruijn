from __future__ import annotations

import os
import random
import sys

import pytest

import py_nanobruijn.check_decl
import py_nanobruijn.level_ops
import py_nanobruijn.tc_context
import py_nanobruijn.tc_defeq
import py_nanobruijn.tc_infer  # noqa: F401

from .config import Config
from .dag import LeanDag, TcCtx
from .level import Level
from .name import Name
from .parser import parse_export_file

sys.setrecursionlimit(10000)

TEST_ROOT = os.path.normpath(
    os.path.join(os.path.dirname(__file__), '..', 'test_resources')
)

# ============================================================
# Helper functions
# ============================================================

def make_ctx() -> TcCtx:
    dag = LeanDag.with_capacity(None, 0)
    return TcCtx(dag)

def insert_name(ctx: TcCtx, s: str, pfx: int = 0) -> int:
    return ctx.dag.insert_name(Name.str(pfx, ctx.dag.insert_string(s)))

def level_n(ctx: TcCtx, lv: int, n: int) -> int:
    for _ in range(n):
        lv = ctx.succ(lv)
    return lv

def param_quick(ctx: TcCtx, s: str) -> int:
    n = insert_name(ctx, s)
    return ctx.dag.insert_level(Level.param(n))

def mk_max(ctx: TcCtx, lv: int, r: int) -> int:
    return ctx.dag.insert_level(Level.max(lv, r))

# nat helper functions (matching Rust src/util.rs)
def nat_sub(x: int, y: int) -> int:
    return 0 if y > x else x - y

def nat_div(x: int, y: int) -> int:
    return 0 if y == 0 else x // y

def nat_mod(x: int, y: int) -> int:
    return x if y == 0 else x % y

def nat_gcd(x: int, y: int) -> int:
    import math
    return math.gcd(x, y)

def nat_xor(x: int, y: int) -> int:
    return x ^ y

def nat_shl(x: int, y: int) -> int:
    return x * (2 ** y)

def nat_shr(x: int, y: int) -> int:
    return x // (2 ** y)

def nat_land(x: int, y: int) -> int:
    return x & y

def nat_lor(x: int, y: int) -> int:
    return x | y

def pred(x: int) -> int:
    return 0 if x == 0 else x - 1

def bitwise(f, n: int, m: int) -> int:
    if n == 0:
        return m if f(False, True) else 0
    if m == 0:
        return n if f(True, False) else 0
    nprime = n // 2
    mprime = m // 2
    b1 = n % 2 == 1
    b2 = m % 2 == 1
    r = bitwise(f, nprime, mprime)
    if f(b1, b2):
        return r + r + 1
    else:
        return r + r


# ============================================================
# Level tests — ported from src/tests/level.rs
# ============================================================

def test_leq_test0():
    ctx = make_ctx()
    z = 0
    s = ctx.succ(z)
    m = mk_max(ctx, s, s)
    assert ctx.leq(s, m)
    assert ctx.leq(m, s)
    assert ctx.eq_antisymm(s, m)

def test_leq_test1():
    ctx = make_ctx()
    z = 0
    s = ctx.succ(z)
    ss = ctx.succ(s)
    im = ctx.imax(ss, z)
    assert ctx.leq(im, z)
    assert ctx.eq_antisymm(z, im)

def test_leq_test2():
    ctx = make_ctx()
    a = param_quick(ctx, "a")
    b = param_quick(ctx, "b")
    assert not ctx.leq(a, b)
    assert not ctx.leq(b, a)

def test_leq_test_imax_imax():
    ctx = make_ctx()
    a = param_quick(ctx, "a")
    b = param_quick(ctx, "b")
    imax_a_b = ctx.imax(a, b)
    s_imax_a_b = ctx.succ(imax_a_b)
    ss_imax_a_b = ctx.succ(s_imax_a_b)
    assert ctx.leq(imax_a_b, imax_a_b)
    assert ctx.leq(imax_a_b, s_imax_a_b)
    assert ctx.leq(imax_a_b, ss_imax_a_b)
    assert ctx.leq(s_imax_a_b, ss_imax_a_b)
    assert not ctx.leq(ss_imax_a_b, imax_a_b)
    assert not ctx.leq(ss_imax_a_b, s_imax_a_b)

def test_leq_test3():
    ctx = make_ctx()
    a = param_quick(ctx, "a")
    b = param_quick(ctx, "b")
    assert not ctx.leq(a, b)
    assert not ctx.leq(b, a)

def test_leq_test4():
    ctx = make_ctx()
    rng = random.Random()
    for _ in range(100):
        small, large = sorted((rng.randint(0, 255), rng.randint(0, 255)))
        p = param_quick(ctx, "p")
        a = level_n(ctx, p, small)
        b = level_n(ctx, p, large)
        assert ctx.leq(a, b)

def test_leq_test5():
    ctx = make_ctx()
    rng = random.Random()
    for _ in range(100):
        small, large = sorted((rng.randint(0, 255), rng.randint(0, 255)))
        p = param_quick(ctx, "p")
        q = param_quick(ctx, "q")
        lhs = level_n(ctx, mk_max(ctx, level_n(ctx, p, small), level_n(ctx, q, small)), small)
        rhs = level_n(ctx, mk_max(ctx, level_n(ctx, p, large), level_n(ctx, q, large)), large)
        assert ctx.leq(lhs, rhs)

def test_leq_test6():
    ctx = make_ctx()
    rng = random.Random()
    for _ in range(100):
        small, large = sorted((rng.randint(0, 255), rng.randint(0, 255)))
        p = param_quick(ctx, "p")
        q = param_quick(ctx, "q")
        lhs = level_n(ctx, ctx.imax(level_n(ctx, p, small), level_n(ctx, q, small)), small)
        rhs = level_n(ctx, ctx.imax(level_n(ctx, p, large), level_n(ctx, q, large)), large)
        assert ctx.leq(lhs, rhs)

def test_leq_test7():
    ctx = make_ctx()
    rng = random.Random()
    for _ in range(100):
        u = rng.randint(0, 255)
        v = rng.randint(0, 255)
        w = rng.randint(0, 255)
        p = param_quick(ctx, "p")
        q = param_quick(ctx, "q")
        lhs = level_n(ctx, ctx.imax(level_n(ctx, p, u), level_n(ctx, q, v + 1)), w)
        rhs = level_n(ctx, mk_max(ctx, level_n(ctx, p, u), level_n(ctx, q, v + 1)), w)
        assert ctx.eq_antisymm(lhs, rhs)

def test_eq_test1():
    ctx = make_ctx()
    z = 0
    s = ctx.succ(z)
    ss = ctx.succ(s)
    m = mk_max(ctx, s, s)
    sm = ctx.succ(m)
    assert ctx.eq_antisymm(ss, sm)

def test_eq_many_test1():
    ctx = make_ctx()
    z = 0
    s = ctx.succ(z)
    ss = ctx.succ(s)
    m = mk_max(ctx, s, s)
    sm = ctx.succ(m)
    ups1 = ctx.dag.insert_uparams((ss,))
    ups2 = ctx.dag.insert_uparams((sm,))
    assert ctx.eq_antisymm_many(ups1, ups2)

def test_debug_test0():
    ctx = make_ctx()
    z = 0
    s = ctx.succ(z)
    ss = ctx.succ(s)
    base, num = ctx.level_succs(ss)
    assert base == z
    assert num == 2

def test_debug_test1():
    ctx = make_ctx()
    z = 0
    s = ctx.succ(z)
    m = mk_max(ctx, s, s)
    sm = ctx.succ(m)
    base, num = ctx.level_succs(sm)
    assert base == m
    assert num == 1


# ============================================================
# Util tests — ported from src/tests/util.rs
# ============================================================

def test_check_empty():
    cf = Config.from_json(os.path.join(TEST_ROOT, 'Empty', 'config.json'))
    assert cf.export_file_path is not None
    export = parse_export_file(cf.export_file_path, cf)
    for declar in export.declars.values():
        export.check_declar(declar)

def test_check_level_index_out_of_order():
    cf = Config.from_json(os.path.join(TEST_ROOT, 'LevelIndexOutOfOrder', 'config.json'))
    assert cf.export_file_path is not None
    export = parse_export_file(cf.export_file_path, cf)
    assert len(export.declars) == 1
    for declar in export.declars.values():
        export.check_declar(declar)

def test_check_sparse_name_index():
    cf = Config.from_json(os.path.join(TEST_ROOT, 'SparseNameIndex', 'config.json'))
    assert cf.export_file_path is not None
    export = parse_export_file(cf.export_file_path, cf)
    assert len(export.declars) == 1
    for declar in export.declars.values():
        export.check_declar(declar)

def test_check_proj_from_prop():
    with pytest.raises(Exception, match="infer_proj"):
        cf = Config.from_json(os.path.join(TEST_ROOT, 'ProjFromProp', 'config.json'))
        cf.unsafe_permit_all_axioms = True
        assert cf.export_file_path is not None
        export = parse_export_file(cf.export_file_path, cf)
        for declar in export.declars.values():
            export.check_declar(declar)

def test_hash_test0():
    ctx = make_ctx()
    rng = random.Random()
    import string as str_mod
    for size in range(100):
        for _ in range(100):
            s = ''.join(rng.choice(str_mod.ascii_letters + str_mod.digits) for _ in range(size))
            lv = ctx.mk_string_lit(s)
            rv = ctx.mk_string_lit(s)
            assert hash(lv) == hash(rv)
            assert lv == rv
    for size in range(100):
        for _ in range(100):
            n = rng.getrandbits(size) if size > 0 else 0
            lv = ctx.mk_nat_lit(n)
            rv = ctx.mk_nat_lit(n)
            assert hash(lv) == hash(rv)
            assert lv == rv


# ============================================================
# NatLit tests — ported from src/tests/natlit.rs
# ============================================================

def test_nat_div_le_self():
    rng = random.Random()
    for size in range(1024):
        for _ in range(10):
            n = rng.getrandbits(size) if size > 0 else 0
            k = rng.getrandbits(size) if size > 0 else 0
            assert nat_div(n, k) <= n

def test_nat_div_eq():
    def nat_div_eq_f(x: int, y: int) -> int:
        if 0 < y <= x:
            return nat_div_eq_f(x - y, y) + 1
        else:
            return 0
    rng = random.Random()
    for size in range(8):
        for _ in range(32):
            x = rng.getrandbits(size) if size > 0 else 0
            y = rng.getrandbits(size) if size > 0 else 0
            assert nat_div_eq_f(x, y) == nat_div(x, y)

def test_nat_shr_eq():
    def nat_shr_eq_f(x: int, y: int) -> int:
        if y == 0:
            return x
        else:
            return nat_shr_eq_f(x, y - 1) // 2
    assert nat_shr(4, 2) == 1
    assert nat_shr(8, 2) == 2
    assert nat_shr(8, 3) == 1
    assert nat_shr(0, 3) == 0
    rng = random.Random()
    for size in range(8):
        for _ in range(32):
            x = rng.getrandbits(size) if size > 0 else 0
            y = rng.getrandbits(size % 6) if size % 6 > 0 else 0
            assert nat_shr_eq_f(x, y) == nat_shr(x, y)

def test_nat_shl_eq():
    def nat_shl_eq_f(x: int, y: int) -> int:
        if y == 0:
            return x
        else:
            return nat_shl_eq_f(2 * x, y - 1)
    assert nat_shl(1, 2) == 4
    assert nat_shl(1, 3) == 8
    assert nat_shl(0, 3) == 0
    assert nat_shl(0xf1, 4) == 0xf10
    rng = random.Random()
    for size in range(8):
        for _ in range(32):
            x = rng.getrandbits(size) if size > 0 else 0
            y = rng.getrandbits(size % 6) if size % 6 > 0 else 0
            assert nat_shl_eq_f(x, y) == nat_shl(x, y)

def test_nat_gcd_eq():
    def nat_gcd_eq_f(m: int, n: int) -> int:
        if m == 0:
            return n
        else:
            return nat_gcd_eq_f(n % m, m)
    assert nat_gcd(10, 15) == 5
    assert nat_gcd(0, 5) == 5
    assert nat_gcd(7, 0) == 7
    assert nat_gcd(1, 0) == 1
    rng = random.Random()
    for size in range(8):
        for _ in range(32):
            x = rng.getrandbits(size) if size > 0 else 0
            y = rng.getrandbits(size) if size > 0 else 0
            g = nat_gcd(x, y)
            assert nat_gcd_eq_f(x, y) == g

def test_nat_xor_eq():
    def spec_xor(x: int, y: int) -> int:
        return bitwise(lambda a, b: a ^ b, x, y)
    rng = random.Random()
    for size in range(5):
        for _ in range(32):
            x = rng.getrandbits(size) if size > 0 else 0
            y = rng.getrandbits(size) if size > 0 else 0
            assert spec_xor(x, y) == nat_xor(x, y)

def test_nat_lor_eq():
    def spec_lor(x: int, y: int) -> int:
        return bitwise(lambda a, b: a or b, x, y)
    rng = random.Random()
    for size in range(5):
        for _ in range(32):
            x = rng.getrandbits(size) if size > 0 else 0
            y = rng.getrandbits(size) if size > 0 else 0
            assert spec_lor(x, y) == nat_lor(x, y)

def test_nat_land_eq():
    def spec_land(x: int, y: int) -> int:
        return bitwise(lambda a, b: a and b, x, y)
    rng = random.Random()
    for size in range(5):
        for _ in range(32):
            x = rng.getrandbits(size) if size > 0 else 0
            y = rng.getrandbits(size) if size > 0 else 0
            assert spec_land(x, y) == nat_land(x, y)

def test_nat_add_eq():
    def nat_add_eq_f(x: int, y: int) -> int:
        if y == 0:
            return x
        else:
            return nat_add_eq_f(x, y - 1) + 1
    rng = random.Random()
    for size in range(8):
        for _ in range(32):
            x = rng.getrandbits(size) if size > 0 else 0
            y = rng.getrandbits(size) if size > 0 else 0
            assert nat_add_eq_f(x, y) == x + y

def test_nat_sub_eq():
    def nat_sub_eq_f(x: int, y: int) -> int:
        if y == 0:
            return x
        else:
            return pred(nat_sub_eq_f(x, y - 1))
    rng = random.Random()
    for size in range(8):
        for _ in range(32):
            x = rng.getrandbits(size) if size > 0 else 0
            y = rng.getrandbits(size) if size > 0 else 0
            assert nat_sub_eq_f(x, y) == nat_sub(x, y)

def test_nat_pow_eq():
    def nat_pow_eq_f(x: int, y: int) -> int:
        if y == 0:
            return 1
        else:
            return (x ** (y - 1)) * x
    rng = random.Random()
    for size in range(8):
        for _ in range(32):
            x = rng.getrandbits(size) if size > 0 else 0
            y = rng.getrandbits(size) if size > 0 else 0
            assert nat_pow_eq_f(x, y) == x ** y

def test_nat_mul_eq():
    def nat_mul_eq_f(x: int, y: int) -> int:
        if y == 0:
            return 0
        else:
            return nat_mul_eq_f(x, y - 1) + x
    rng = random.Random()
    for size in range(8):
        for _ in range(32):
            x = rng.getrandbits(size) if size > 0 else 0
            y = rng.getrandbits(size) if size > 0 else 0
            assert nat_mul_eq_f(x, y) == x * y

def test_nat_ble_eq():
    def nat_ble_eq_f(x: int, y: int) -> bool:
        if x == 0:
            return True
        elif y == 0:
            return False
        else:
            return nat_ble_eq_f(pred(x), pred(y))
    rng = random.Random()
    for size in range(8):
        for _ in range(32):
            x = rng.getrandbits(size) if size > 0 else 0
            y = rng.getrandbits(size) if size > 0 else 0
            assert nat_ble_eq_f(x, y) == (x <= y)

def test_nat_mod_eq():
    def nat_mod_eq_f(x: int, y: int) -> int:
        if 0 < y <= x:
            return nat_mod_eq_f(x - y, y)
        else:
            return x
    rng = random.Random()
    for size in range(8):
        for _ in range(32):
            x = rng.getrandbits(size) if size > 0 else 0
            y = rng.getrandbits(size) if size > 0 else 0
            assert nat_mod_eq_f(x, y) == nat_mod(x, y)

def test_nat_div_add_mod():
    rng = random.Random()
    for size in range(128):
        for _ in range(32):
            n = rng.getrandbits(size) if size > 0 else 0
            m = rng.getrandbits(size) if size > 0 else 0
            m_div_n = nat_div(m, n)
            m_mod_n = nat_mod(m, n)
            nat_mul_div = n * m_div_n
            assert nat_mul_div + m_mod_n == m

def test_nat_mod_eq_sub_mod():
    rng = random.Random()
    for size in range(128):
        iterations = 0
        while iterations < 32:
            a = rng.getrandbits(size) if size > 0 else 0
            b = rng.getrandbits(size) if size > 0 else 0
            if a >= b:
                iterations += 1
                assert nat_mod(a, b) == nat_mod(a - b, b)
