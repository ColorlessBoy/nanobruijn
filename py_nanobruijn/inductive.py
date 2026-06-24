from __future__ import annotations
from typing import Dict

from .dag import TcCtx
from .env import (
    Declar, InductiveDecl, Env, EnvLimit,
)
from .ptr import ExprPtr, NamePtr
from .tc_whnf import TypeChecker


def check_inductive_declar(self, d: InductiveDecl, declars: Dict[NamePtr, Declar]):
    """Check an inductive declaration.

    Validates the inductive types in the mutual block.
    Constructors and Recursors are checked separately as their own Declar types.
    """
    if not isinstance(d, InductiveDecl):
        raise TypeError(f"expected InductiveDecl, got {type(d)}")

    # Collect all names in this mutual block
    mutual_names = _mutual_names(d)

    # Find the last mutual decl's position for env cutoff
    last_idx = _find_last_mutual_index(declars, mutual_names)
    env = Env(declars=declars, limit=EnvLimit('by_index', last_idx + 1))
    env.temp_declars = {name: declars[name] for name in mutual_names}

    ctx = TcCtx(self.dag)
    ctx.export_file = self

    # Check each inductive type
    for ind_data in d.inductives:
        _check_inductive_type(self, ctx, env, ind_data, declars, mutual_names)

    # Check each constructor
    for ctor_data in d.constructors:
        _check_constructor_type(self, ctx, env, ctor_data, declars, mutual_names, d)

    # Check each recursor
    for rec_data in d.recursors:
        _check_recursor_type(self, ctx, env, rec_data, declars, mutual_names, d)


def _mutual_names(d):
    names = set()
    for ind_data in d.inductives:
        names.add(ind_data.info.name)
    for ctor_data in d.constructors:
        names.add(ctor_data.info.name)
    for rec_data in d.recursors:
        names.add(rec_data.info.name)
    return names


def _find_last_mutual_index(declars, mutual_names):
    last_idx = -1
    for i, name in enumerate(declars):
        if name in mutual_names:
            last_idx = i
    return last_idx


def _make_tc(self, ctx, env, info):
    tc = TypeChecker(ctx, env, declar_info=info)
    return tc


def _check_inductive_type(self, ctx, env, ind_data, declars, mutual_names):
    """Check that ind_data.info.ty is a valid Sort."""
    tc = _make_tc(self, ctx, env, ind_data.info)
    tc.check_declar_info(
        _wrap_info_as_declar(ind_data.info)
    )
    # Verify the inductive's level parameters
    for lv in ctx.read_levels(ind_data.info.uparams):
        assert ctx.all_uparams_defined(lv, ind_data.info.uparams)


def _check_constructor_type(self, ctx, env, ctor_data, declars, mutual_names, d):
    """Check the constructor's type."""
    tc = _make_tc(self, ctx, env, ctor_data.info)
    tc.check_declar_info(
        _wrap_info_as_declar(ctor_data.info)
    )
    ind_name = ctor_data.inductive_name
    # Verify the inductive type exists
    assert ind_name in declars, f"inductive {ind_name} not found for constructor"
    # Verify the constructor type ends in the inductive type
    ctor_ty = ExprPtr.closed(ctor_data.info.ty)
    _check_ctor_target_type(tc, ctx, ctor_ty, ind_name, ctor_data.num_params)


def _check_ctor_target_type(tc, ctx, ctor_ty, ind_name, num_params):
    """Verify that the constructor type is a Pi telescope ending in `ind_name`."""
    cur = ctor_ty
    # Peel off params
    for _ in range(num_params):
        cur = tc.whnf(cur)
        viewed = ctx.view_expr(cur)
        if viewed.tag != 'Pi':
            raise ValueError(f"constructor params exhausted for {ind_name}")
        cur = viewed.children[3]
    # Peel remaining Pi binder types (fields)
    while True:
        cur = tc.whnf(cur)
        viewed = ctx.view_expr(cur)
        if viewed.tag == 'Pi':
            cur = viewed.children[3]
        else:
            break
    # End should be an application of the inductive type
    unfolded = ctx.unfold_const_apps(cur)
    if unfolded is None:
        raise ValueError(f"constructor does not end in application of {ind_name}")
    _, ctor_ind_name, _, _ = unfolded
    if ctor_ind_name != ind_name:
        raise ValueError(
            f"constructor ends in wrong inductive: "
            f"expected {ind_name}, got {ctor_ind_name}"
        )


def _check_recursor_type(self, ctx, env, rec_data, declars, mutual_names, d):
    """Check the recursor's type and rules."""
    tc = _make_tc(self, ctx, env, rec_data.info)
    tc.check_declar_info(
        _wrap_info_as_declar(rec_data.info)
    )
    for ind_name in rec_data.all_inductives:
        assert ind_name in declars, f"inductive {ind_name} not found for recursor"
    # Validate the recursor type structure
    rec_ty = ExprPtr.closed(rec_data.info.ty)
    _check_recursor_type_structure(tc, ctx, rec_data, rec_ty)


def _check_recursor_type_structure(tc, ctx, rec_data, rec_ty):
    """Validate the recursor's type telescope structure."""
    expected_tele = (
        rec_data.num_params
        + rec_data.num_motives
        + rec_data.num_minors
        + rec_data.num_indices
        + 1
    )
    cur = rec_ty
    count = 0
    while True:
        cur = tc.whnf(cur)
        viewed = ctx.view_expr(cur)
        if viewed.tag == 'Pi':
            count += 1
            cur = viewed.children[3]
        else:
            break
    if count != expected_tele:
        raise ValueError(
            f"recursor telescope size mismatch: "
            f"expected {expected_tele}, got {count}"
        )


def _wrap_info_as_declar(info):
    """Minimal Declar wrapper to use TypeChecker.check_declar_info."""
    from .env import Axiom
    return Axiom(info=info, is_unsafe=False)


# Patch onto ExportFile
from .parser import ExportFile  # noqa: E402
ExportFile.check_inductive_declar = check_inductive_declar  # type: ignore[assignment]
