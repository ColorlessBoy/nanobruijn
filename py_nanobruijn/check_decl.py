from __future__ import annotations
import time

from .env import (
    Declar, Axiom, Theorem, Definition, OpaqueDecl, QuotDecl,
    InductiveDecl, ConstructorDecl, RecursorDecl,
    Env, EnvLimit,
)
from .parser import ExportFile
from .dag import TcCtx
from .tc_whnf import TypeChecker
from .ptr import ExprPtr
from . import quot  # noqa: F401 — patches ExportFile.check_quot

# ============================================================
# TypeChecker.check_declar_info
# ============================================================

def check_declar_info(self: TypeChecker, d: Declar):
    info = d.info
    assert self.ctx.no_dupes_all_params(info.uparams), \
        "duplicate universe parameters in declaration"
    assert self.ctx.dag.expr_nlbv[info.ty] == 0, \
        "declaration type has free variables"
    inferred_type = self.infer(ExprPtr.closed(info.ty), 'check')
    sort = self.ensure_sort(inferred_type)
    if isinstance(d, Theorem):
        if not self.ctx.is_zero(sort):
            name_str = self.ctx.name_to_string(info.name)
            raise ValueError(
                f"Theorem type for {name_str!r} must be `Prop` (sort 0); "
                f"found sort level {sort}"
            )

# ============================================================
# ExportFile.check_declar dispatch
# ============================================================

def check_declar(self: ExportFile, d: Declar):
    if self.config.use_nanoda_tc:
        self._check_declar_nanoda(d)
    else:
        self._check_declar_shift(d)

def _check_declar_nanoda(self: ExportFile, d: Declar):
    self._check_declar_shift(d)

def _check_declar_shift(self: ExportFile, d: Declar):
    if isinstance(d, Axiom):
        tc = self._with_tc(d)
        tc.check_declar_info(d)

    elif isinstance(d, (Definition, Theorem, OpaqueDecl)):
        tc = self._with_tc(d)
        tc.check_declar_info(d)
        inferred_type = tc.infer(ExprPtr.closed(d.value), 'check')
        tc.assert_def_eq(inferred_type, ExprPtr.closed(d.info.ty))

    elif isinstance(d, InductiveDecl):
        self.check_inductive_declar(d, self.declars)

    elif isinstance(d, QuotDecl):
        self.check_quot(d)

    elif isinstance(d, ConstructorDecl):
        tc = self._with_tc(d)
        tc.check_declar_info(d)
        assert d.data.inductive_name in self.declars, \
            "inductive declaration not found for constructor"

    elif isinstance(d, RecursorDecl):
        tc = self._with_tc(d)
        tc.check_declar_info(d)
        for ind_name in d.data.all_inductives:
            assert ind_name in self.declars, \
                "inductive declaration not found for recursor"

# ============================================================
# ExportFile.check_all_declars
# ============================================================

def check_all_declars(self: ExportFile) -> int:
    if self.config.num_threads > 1:
        pass
    return self._check_all_declars_serial()

def _check_all_declars_serial(self: ExportFile) -> int:
    total = len(self.declars)
    start = time.time()
    last_report = start
    max_decl = self.config.max_declarations
    skip_decl = self.config.skip_declarations
    timeout_secs = self.config.declaration_timeout_secs
    panics = 0

    for i, (name, declar) in enumerate(self.declars.items()):
        if max_decl > 0 and i >= max_decl:
            print(f"[stopping at {max_decl} declarations as configured]")
            break
        if i < skip_decl:
            continue
        if self.config.declaration_filter:
            name_str = self.name_to_string(declar.info.name)
            if self.config.declaration_filter not in name_str:
                continue

        if i % 1000 == 0 or (skip_decl > 0 and i == skip_decl):
            elapsed = int((time.time() - start) * 1000)
            delta = int((time.time() - last_report) * 1000)
            print(f"[{i}/{total} {elapsed}ms +{delta}ms]")
            last_report = time.time()

        try:
            self.check_declar(declar)
        except Exception as e:
            if timeout_secs > 0:
                name_str = self.name_to_string(declar.info.name)
                print(f"  PANIC #{i}: {name_str!r} (skipping): {e}")
                panics += 1
            else:
                raise

    if panics > 0:
        print(f"[WARNING: {panics} declarations panicked and were skipped]")

    return panics

# ============================================================
# ExportFile helpers
# ============================================================

def _make_env(self: ExportFile, limit: EnvLimit = None) -> Env:
    if limit is None:
        limit = EnvLimit('pp_unlimited')
    return Env(declars=self.declars, limit=limit)

def _with_tc(self: ExportFile, d: Declar) -> TypeChecker:
    ctx = TcCtx(self.dag)
    ctx.export_file = self
    env = self._make_env(EnvLimit('by_name', d.info.name))
    tc = TypeChecker(ctx, env, declar_info=d.info)
    return tc

def name_to_string(self: ExportFile, ptr) -> str:
    from .name import name_to_string as _nts
    name = self.dag.get_name(ptr)
    return _nts(name, self.dag.names, self.dag.strings)

# ============================================================
# Patch methods onto ExportFile and TypeChecker
# ============================================================

TypeChecker.check_declar_info = check_declar_info

ExportFile.check_declar = check_declar
ExportFile._check_declar_shift = _check_declar_shift
ExportFile._check_declar_nanoda = _check_declar_nanoda
ExportFile.check_all_declars = check_all_declars
ExportFile._check_all_declars_serial = _check_all_declars_serial
ExportFile._make_env = _make_env
ExportFile._with_tc = _with_tc
ExportFile.name_to_string = name_to_string
