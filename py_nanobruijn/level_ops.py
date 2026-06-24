from __future__ import annotations

from .level import Level
from .ptr import LevelPtr, LevelsPtr, NamePtr, ExprPtr
from .dag import TcCtx


def level_succs(self, lv: LevelPtr) -> tuple[LevelPtr, int]:
    num_succs = 0
    while True:
        level = self.dag.get_level(lv)
        if level.tag != 'Succ':
            break
        lv = level.pred
        num_succs += 1
    return (lv, num_succs)


def _is_one(self, lv: LevelPtr) -> bool:
    level = self.dag.get_level(lv)
    return level.tag == 'Succ' and self.is_zero(level.pred)


def _is_param(self, lv: LevelPtr) -> bool:
    return self.dag.get_level(lv).tag == 'Param'


def _is_any_max(self, lv: LevelPtr) -> bool:
    tag = self.dag.get_level(lv).tag
    return tag in ('Max', 'IMax')


def _combining(self, lv: LevelPtr, r: LevelPtr) -> LevelPtr:
    l_level = self.dag.get_level(lv)
    r_level = self.dag.get_level(r)
    if l_level.tag == 'Zero':
        return r
    if r_level.tag == 'Zero':
        return lv
    if l_level.tag == 'Succ' and r_level.tag == 'Succ':
        pred = self._combining(l_level.pred, r_level.pred)
        return self.dag.insert_level(Level.succ(pred))
    return self.dag.insert_level(Level.max(lv, r))


def simplify(self, ptr: LevelPtr) -> LevelPtr:
    level = self.dag.get_level(ptr)
    tag = level.tag
    if tag in ('Zero', 'Param'):
        return ptr
    if tag == 'Succ':
        val = self.simplify(level.pred)
        return self.dag.insert_level(Level.succ(val))
    if tag == 'Max':
        l_simp = self.simplify(level.left)
        r_simp = self.simplify(level.right)
        return self._combining(l_simp, r_simp)
    if tag == 'IMax':
        l_simp = self.simplify(level.left)
        r_simp = self.simplify(level.right)
        if self.is_zero(l_simp) or self._is_one(l_simp):
            return r_simp
        r_tag = self.dag.get_level(r_simp).tag
        if r_tag == 'Zero':
            return r_simp
        if r_tag == 'Succ':
            return self._combining(l_simp, r_simp)
        return self.dag.insert_level(Level.imax(l_simp, r_simp))
    return ptr


def subst_level(self, level: LevelPtr, ks: LevelsPtr, vs: LevelsPtr) -> LevelPtr:
    lvl = self.dag.get_level(level)
    tag = lvl.tag
    if tag == 'Zero':
        return 0
    if tag == 'Succ':
        val = self.subst_level(lvl.pred, ks, vs)
        return self.dag.insert_level(Level.succ(val))
    if tag == 'Max':
        l_prime = self.subst_level(lvl.left, ks, vs)
        r_prime = self.subst_level(lvl.right, ks, vs)
        return self.dag.insert_level(Level.max(l_prime, r_prime))
    if tag == 'IMax':
        l_prime = self.subst_level(lvl.left, ks, vs)
        r_prime = self.subst_level(lvl.right, ks, vs)
        return self.dag.insert_level(Level.imax(l_prime, r_prime))
    if tag == 'Param':
        k_tuple = self.dag.uparams[ks]
        v_tuple = self.dag.uparams[vs]
        for k, v in zip(k_tuple, v_tuple):
            if level == k:
                return v
        return level
    return level


def subst_levels(self, uparams: LevelsPtr, ks: LevelsPtr, vs: LevelsPtr) -> LevelsPtr:
    out = tuple(self.subst_level(lv, ks, vs) for lv in self.dag.uparams[uparams])
    return self.dag.insert_uparams(out)


def _subst_simp(self, level: LevelPtr, ks: LevelsPtr, vs: LevelsPtr) -> LevelPtr:
    lv = self.subst_level(level, ks, vs)
    return self.simplify(lv)


def _leq_imax_by_cases(self, param: LevelPtr, lhs: LevelPtr, rhs: LevelPtr, diff: int) -> bool:
    zero = 0
    succ_param = self.dag.insert_level(Level.succ(param))
    zero_slice = self.dag.insert_uparams((zero,))
    succ_param_slice = self.dag.insert_uparams((succ_param,))
    param_slice = self.dag.insert_uparams((param,))

    lhs_0 = self._subst_simp(lhs, param_slice, zero_slice)
    rhs_0 = self._subst_simp(rhs, param_slice, zero_slice)
    lhs_s = self._subst_simp(lhs, param_slice, succ_param_slice)
    rhs_s = self._subst_simp(rhs, param_slice, succ_param_slice)

    return self._leq_core(lhs_0, rhs_0, diff) and self._leq_core(lhs_s, rhs_s, diff)


def _leq_core(self, l_in: LevelPtr, r_in: LevelPtr, diff: int) -> bool:
    lv = self.dag.get_level(l_in)
    r = self.dag.get_level(r_in)

    lt, rt = lv.tag, r.tag

    if lt == 'Zero' and diff >= 0:
        return True

    if rt == 'Zero' and diff < 0:
        return False

    if lt == 'Param' and rt == 'Param':
        return lv.param_name == r.param_name and diff >= 0

    if lt == 'Param' and rt == 'Zero':
        return False

    if lt == 'Zero' and rt == 'Param':
        return diff >= 0

    if lt == 'Succ':
        return self._leq_core(lv.pred, r_in, diff - 1)

    if rt == 'Succ':
        return self._leq_core(l_in, r.pred, diff + 1)

    if lt == 'Max':
        return self._leq_core(lv.left, r_in, diff) and self._leq_core(lv.right, r_in, diff)

    if rt == 'Max' and lt in ('Param', 'Zero'):
        return self._leq_core(l_in, r.left, diff) or self._leq_core(l_in, r.right, diff)

    if lt == 'IMax' and rt == 'IMax' and lv.left == r.left and lv.right == r.right and diff >= 0:
        return True

    if lt == 'IMax' and self._is_param(lv.right):
        return self._leq_imax_by_cases(lv.right, l_in, r_in, diff)

    if rt == 'IMax' and self._is_param(r.right):
        return self._leq_imax_by_cases(r.right, l_in, r_in, diff)

    if lt == 'IMax' and self._is_any_max(lv.right):
        b_level = self.dag.get_level(lv.right)
        if b_level.tag == 'IMax':
            new_lhs = self.dag.insert_level(Level.imax(lv.left, b_level.right))
            new_rhs = self.dag.insert_level(Level.imax(b_level.left, b_level.right))
            new_max = self.dag.insert_level(Level.max(new_lhs, new_rhs))
            return self._leq_core(new_max, r_in, diff)
        if b_level.tag == 'Max':
            new_lhs = self.dag.insert_level(Level.imax(lv.left, b_level.left))
            new_rhs = self.dag.insert_level(Level.imax(lv.left, b_level.right))
            new_max = self.dag.insert_level(Level.max(new_lhs, new_rhs))
            new_max = self.simplify(new_max)
            return self._leq_core(new_max, r_in, diff)
        raise ValueError("unexpected level in IMax right")

    if rt == 'IMax' and self._is_any_max(r.right):
        y_level = self.dag.get_level(r.right)
        if y_level.tag == 'IMax':
            new_lhs = self.dag.insert_level(Level.imax(r.left, y_level.right))
            new_rhs = self.dag.insert_level(Level.imax(y_level.left, y_level.right))
            new_max = self.dag.insert_level(Level.max(new_lhs, new_rhs))
            return self._leq_core(l_in, new_max, diff)
        if y_level.tag == 'Max':
            new_lhs = self.dag.insert_level(Level.imax(r.left, y_level.left))
            new_rhs = self.dag.insert_level(Level.imax(r.left, y_level.right))
            new_rhs = self.dag.insert_level(Level.max(new_lhs, new_rhs))
            new_rhs = self.simplify(new_rhs)
            return self._leq_core(l_in, new_rhs, diff)
        raise ValueError("unexpected level in IMax right")

    raise ValueError(f"unhandled case in leq_core: (lv={lt}, r={rt})")


def leq(self, lv: LevelPtr, r: LevelPtr) -> bool:
    l_prime = self.simplify(lv)
    r_prime = self.simplify(r)
    return self._leq_core(l_prime, r_prime, 0)


def eq_antisymm(self, lv: LevelPtr, r: LevelPtr) -> bool:
    return self.leq(lv, r) and self.leq(r, lv)


def eq_antisymm_many(self, xs: LevelsPtr, ys: LevelsPtr) -> bool:
    xs_levels = self.dag.uparams[xs]
    ys_levels = self.dag.uparams[ys]
    if len(xs_levels) != len(ys_levels):
        return False
    return all(self.eq_antisymm(x, y) for x, y in zip(xs_levels, ys_levels))


def is_zero(self, level: LevelPtr) -> bool:
    return self.leq(level, 0)


def is_nonzero(self, level: LevelPtr) -> bool:
    zero = 0
    one = self.dag.insert_level(Level.succ(zero))
    return self.leq(one, level)


def contains_param(self, uparams: LevelsPtr, candidate: NamePtr) -> bool:
    for lv in self.dag.uparams[uparams]:
        lvl = self.dag.get_level(lv)
        if lvl.tag == 'Param' and lvl.param_name == candidate:
            return True
    return False


def all_uparams_defined(self, level: LevelPtr, params: LevelsPtr) -> bool:
    lvl = self.dag.get_level(level)
    if lvl.tag == 'Zero':
        return True
    if lvl.tag == 'Succ':
        return self.all_uparams_defined(lvl.pred, params)
    if lvl.tag in ('Max', 'IMax'):
        return self.all_uparams_defined(lvl.left, params) and self.all_uparams_defined(lvl.right, params)
    if lvl.tag == 'Param':
        return level in self.dag.uparams[params]
    return True


def no_dupes_all_params(self, ls: LevelsPtr) -> bool:
    seen = set()
    for lv in self.dag.uparams[ls]:
        lvl = self.dag.get_level(lv)
        if lvl.tag != 'Param':
            return False
        if lv in seen:
            return False
        seen.add(lv)
    return True


def succ(self, level: LevelPtr) -> LevelPtr:
    return self.dag.insert_level(Level.succ(level))


def imax(self, lv: LevelPtr, r: LevelPtr) -> LevelPtr:
    return self.dag.insert_level(Level.imax(lv, r))


def read_level(self, ptr: LevelPtr):
    return self.dag.get_level(ptr)


def read_levels(self, ptr: LevelsPtr):
    return self.dag.uparams[ptr]


def prop(self) -> ExprPtr:
    return self.mk_sort(0)


# Patch all functions as methods on TcCtx
TcCtx.level_succs = level_succs
TcCtx.simplify = simplify
TcCtx.subst_level = subst_level
TcCtx.subst_levels = subst_levels
TcCtx.leq = leq
TcCtx.eq_antisymm = eq_antisymm
TcCtx.eq_antisymm_many = eq_antisymm_many
TcCtx.is_zero = is_zero
TcCtx.is_nonzero = is_nonzero
TcCtx.contains_param = contains_param
TcCtx.all_uparams_defined = all_uparams_defined
TcCtx.no_dupes_all_params = no_dupes_all_params
TcCtx.succ = succ
TcCtx.imax = imax
TcCtx.read_level = read_level
TcCtx.read_levels = read_levels

# Private helpers
TcCtx._is_one = _is_one
TcCtx._is_param = _is_param
TcCtx._is_any_max = _is_any_max
TcCtx._combining = _combining
TcCtx._subst_simp = _subst_simp
TcCtx._leq_imax_by_cases = _leq_imax_by_cases
TcCtx._leq_core = _leq_core
