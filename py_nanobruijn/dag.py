from __future__ import annotations

from .name import Name
from .level import Level
from .expr import Expr
from .ptr import ExprPtr, CorePtr, LevelPtr, LevelsPtr, NamePtr


class LeanDag:
    """Hash-consing storage for names, levels, expressions.

    Analogous to ``LeanDag<'a>`` in Rust.
    Uses append-only list + dict for O(1) dedup lookup.
    """

    __slots__ = (
        'names', 'name_map',
        'levels', 'level_map',
        'exprs', 'expr_map',
        'expr_nlbv',
        'uparams', 'uparam_map',
        'strings', 'string_map',
        'bignums', 'bignum_map',
        '_seed_name_count', '_seed_level_count', '_seed_expr_count',
    )

    def __init__(self, config=None):
        self.names: list[Name] = []
        self.name_map: dict[Name, int] = {}

        self.levels: list[Level] = []
        self.level_map: dict[Level, int] = {}

        self.exprs: list[Expr] = []
        self.expr_map: dict[Expr, int] = {}
        self.expr_nlbv: list[int] = []

        self.uparams: list[tuple[int, ...]] = []
        self.uparam_map: dict[tuple[int, ...], int] = {}

        self.strings: list[str] = []
        self.string_map: dict[str, int] = {}

        self.bignums: list = []
        self.bignum_map: dict = {}

        self._seed_name_count = 0
        self._seed_level_count = 0
        self._seed_expr_count = 0

    # ---- Name ops ----

    def insert_name(self, name: Name) -> int:
        idx = self.name_map.get(name)
        if idx is not None:
            return idx
        idx = len(self.names)
        self.names.append(name)
        self.name_map[name] = idx
        return idx

    def get_name(self, ptr: NamePtr) -> Name:
        return self.names[ptr]

    # ---- Level ops ----

    def insert_level(self, level: Level) -> int:
        idx = self.level_map.get(level)
        if idx is not None:
            return idx
        idx = len(self.levels)
        self.levels.append(level)
        self.level_map[level] = idx
        return idx

    def get_level(self, ptr: LevelPtr) -> Level:
        return self.levels[ptr]

    # ---- Expr ops ----

    def insert_expr(self, expr: Expr) -> tuple[int, bool]:
        idx = self.expr_map.get(expr)
        if idx is not None:
            return idx, False
        nlbv = self._compute_nlbv(expr)
        idx = len(self.exprs)
        self.exprs.append(expr)
        self.expr_map[expr] = idx
        self.expr_nlbv.append(nlbv)
        return idx, True

    def get_expr(self, ptr: CorePtr) -> Expr:
        return self.exprs[ptr]

    def _compute_nlbv(self, expr: Expr) -> int:
        def eff(ep: ExprPtr) -> int:
            if ep.is_closed():
                return 0
            core_nlbv = self.expr_nlbv[ep.core]
            if core_nlbv == 0:
                return 0
            return core_nlbv + ep.shift

        tag = expr.tag
        if tag in ('Sort', 'Const', 'Local', 'StringLit', 'NatLit'):
            return 0
        if tag == 'Var':
            return expr.children[0] + 1
        if tag == 'App':
            return max(eff(expr.children[0]), eff(expr.children[1]))
        if tag in ('Pi', 'Lambda'):
            bt_nlbv = eff(expr.children[2])
            body_nlbv = eff(expr.children[3])
            body_nlbv = body_nlbv - 1 if body_nlbv > 0 else 0
            return max(bt_nlbv, body_nlbv)
        if tag == 'Let':
            bt_nlbv = eff(expr.children[1])
            val_nlbv = eff(expr.children[2])
            body_nlbv = eff(expr.children[3])
            body_nlbv = body_nlbv - 1 if body_nlbv > 0 else 0
            return max(bt_nlbv, val_nlbv, body_nlbv)
        if tag == 'Proj':
            return eff(expr.children[2])
        return 0

    # ---- Uparams ops ----

    def insert_uparams(self, levels: tuple[int, ...]) -> int:
        idx = self.uparam_map.get(levels)
        if idx is not None:
            return idx
        idx = len(self.uparams)
        self.uparams.append(levels)
        self.uparam_map[levels] = idx
        return idx

    # ---- String ops ----

    def insert_string(self, s: str) -> int:
        idx = self.string_map.get(s)
        if idx is not None:
            return idx
        idx = len(self.strings)
        self.strings.append(s)
        self.string_map[s] = idx
        return idx

    # ---- Bignum ops ----

    def insert_bignum(self, n) -> int:
        idx = self.bignum_map.get(n)
        if idx is not None:
            return idx
        idx = len(self.bignums)
        self.bignums.append(n)
        self.bignum_map[n] = idx
        return idx

    # ---- Seed / capacity / clear ----

    @staticmethod
    def with_capacity(config, estimated_exprs: int = 0) -> LeanDag:
        dag = LeanDag(config)

        name_anon = Name.anon()
        dag.name_map[name_anon] = 0
        dag.names.append(name_anon)

        level_zero = Level.zero()
        dag.level_map[level_zero] = 0
        dag.levels.append(level_zero)

        dag._seed_name_count = 1
        dag._seed_level_count = 1
        dag._seed_expr_count = 0

        return dag

    def clear_for_reuse(self):
        self.names.clear()
        self.name_map.clear()
        self.levels.clear()
        self.level_map.clear()
        self.exprs.clear()
        self.expr_map.clear()
        self.expr_nlbv.clear()
        self.uparams.clear()
        self.uparam_map.clear()
        self.strings.clear()
        self.string_map.clear()
        self.bignums.clear()
        self.bignum_map.clear()

        name_anon = Name.anon()
        self.name_map[name_anon] = 0
        self.names.append(name_anon)

        level_zero = Level.zero()
        self.level_map[level_zero] = 0
        self.levels.append(level_zero)

        self._seed_name_count = 1
        self._seed_level_count = 1
        self._seed_expr_count = 0


class TcCtx:
    """Type checking context. Wraps the DAG.

    Analogous to ``TcCtx<'t, 'p>`` in Rust (basic version).
    """

    __slots__ = ('dag', 'export_file', 'local_depth', '_name_cache')

    def __init__(self, dag: LeanDag):
        self.dag = dag
        self.export_file = None
        self.local_depth = 0
        self._name_cache = {}

    # --- Methods patched by level_ops.py ---
    def simplify(self, lv: LevelPtr) -> LevelPtr: ...
    def subst_level(self, lv: LevelPtr, ks: LevelsPtr, vs: LevelsPtr) -> LevelPtr: ...
    def subst_levels(self, uparams: LevelsPtr, ks: LevelsPtr, vs: LevelsPtr) -> LevelsPtr: ...
    def leq(self, l1: LevelPtr, l2: LevelPtr) -> bool: ...
    def eq_antisymm(self, l1: LevelPtr, l2: LevelPtr) -> bool: ...
    def eq_antisymm_many(self, v1, v2) -> bool: ...
    def is_zero(self, lv: LevelPtr) -> bool: ...
    def is_nonzero(self, lv: LevelPtr) -> bool: ...
    def contains_param(self, uparams: LevelsPtr, candidate: NamePtr) -> bool: ...
    def all_uparams_defined(self, lv: LevelPtr, uparams: LevelsPtr) -> bool: ...
    def level_succs(self, lv: LevelPtr) -> tuple: ...
    def no_dupes_all_params(self, ls: LevelsPtr) -> bool: ...
    def imax(self, lv: LevelPtr, rv: LevelPtr) -> LevelPtr: ...
    def succ(self, lv: LevelPtr) -> LevelPtr: ...
    def read_level(self, lv: LevelPtr): ...
    def read_levels(self, uparams: LevelsPtr): ...
    def prop(self) -> ExprPtr: ...

    # --- Methods patched by tc_context.py ---
    def shift_expr(self, e: ExprPtr, k: int) -> ExprPtr: ...
    def inst(self, e: ExprPtr, s: int, u: ExprPtr) -> ExprPtr: ...
    def inst_beta(self, e: ExprPtr, args: list) -> ExprPtr: ...
    def inst_forall_params(self, e: ExprPtr, args: list) -> ExprPtr: ...
    def abstr(self, e: ExprPtr) -> ExprPtr: ...
    def abstr_pi(self, body, name, style, binder_type) -> ExprPtr: ...
    def abstr_lambda(self, body, name, style, binder_type) -> ExprPtr: ...
    def abstr_levels(self, e: ExprPtr, params: list) -> ExprPtr: ...
    def unfold_apps(self, e: ExprPtr) -> tuple: ...
    def unfold_const_apps(self, e: ExprPtr): ...
    def unfold_pi(self, e: ExprPtr): ...
    def unfold_pi_telescope(self, e: ExprPtr): ...
    def view_pi_head(self, e: ExprPtr): ...
    def view_expr(self, e: ExprPtr): ...
    def mk_var(self, dbj_idx: int) -> ExprPtr: ...
    def mk_sort(self, level: LevelPtr) -> ExprPtr: ...
    def mk_const(self, name, levels) -> ExprPtr: ...
    def mk_app(self, fun: ExprPtr, arg: ExprPtr) -> ExprPtr: ...
    def mk_pi(self, name, style, binder_type, body) -> ExprPtr: ...
    def mk_lambda(self, name, style, binder_type, body) -> ExprPtr: ...
    def mk_let(self, name, binder_type, val, body, nondep=False) -> ExprPtr: ...
    def mk_proj(self, type_name, idx, structure) -> ExprPtr: ...
    def mk_string_lit(self, s) -> ExprPtr: ...
    def mk_nat_lit(self, n) -> ExprPtr: ...
    def foldl_apps(self, head: ExprPtr, args: list) -> ExprPtr: ...
    def mk_sort_zero(self) -> ExprPtr: ...
    def mk_sort_one(self) -> ExprPtr: ...
    def mk_shift(self, inner: ExprPtr, amount: int) -> ExprPtr: ...
    def name_to_string(self, ptr) -> str: ...
    def debug_print(self, item): ...
    def subst_expr_levels(self, e, params, vals): ...
    def try_const_info(self, e): ...
    def is_app(self, e: ExprPtr) -> bool: ...
    def is_pi(self, e: ExprPtr) -> bool: ...
    def is_lambda(self, e: ExprPtr) -> bool: ...
    def is_proj(self, e: ExprPtr) -> bool: ...
    def unfold_lambda(self, e: ExprPtr): ...
    def view_expr_pair(self, e1, e2): ...

    def get_name(self, ptr: NamePtr) -> Name:
        return self.dag.get_name(ptr)

    def get_level(self, ptr: LevelPtr) -> Level:
        return self.dag.get_level(ptr)

    def get_expr(self, ptr: CorePtr) -> Expr:
        return self.dag.get_expr(ptr)

    def nlbv(self, e: ExprPtr) -> int:
        if e.is_closed():
            return 0
        core_nlbv = self.dag.expr_nlbv[e.core]
        if core_nlbv == 0:
            return 0
        return core_nlbv + e.shift
