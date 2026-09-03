from __future__ import annotations

from .dag import TcCtx
from .env import (
    ConstructorDecl,
    Declar,
    Env,
    EnvLimit,
    InductiveDecl,
)
from .ptr import ExprPtr, NamePtr
from .tc_whnf import TypeChecker


def check_inductive_declaration(export, d: InductiveDecl, declars: dict[NamePtr, Declar]):
    """Check an inductive declaration.

    Validates the inductive types in the mutual block.
    Constructors and Recursors are checked separately as their own Declar types.
    """
    if not isinstance(d, InductiveDecl):
        raise TypeError(f"expected InductiveDecl, got {type(d)}")

    # Collect all names in this mutual block
    mutual_names = _mutual_names(d)

    # PR #22 alignment: recompute is_recursive from the constructor telescopes
    # and assert it matches the export file's isRec flag.
    for ind_data in d.inductives:
        computed = _computed_is_recursive(export.dag, ind_data, declars)
        if ind_data.is_rec != computed:
            raise ValueError(
                f"inductive {ind_data.info.name}: is_rec flag mismatch: "
                f"export says {ind_data.is_rec}, constructors imply {computed}"
            )

    # Find the last mutual decl's position for env cutoff
    last_idx = _find_last_mutual_index(declars, mutual_names)
    env = Env(declars=declars, limit=EnvLimit('by_index', last_idx + 1))
    env.temp_declars = {name: declars[name] for name in mutual_names}

    ctx = TcCtx(export.dag)
    ctx.export_file = export

    # Check each inductive type
    for ind_data in d.inductives:
        _check_inductive_type(export, ctx, env, ind_data, declars, mutual_names)

    # Check each constructor
    for ctor_data in d.constructors:
        _check_constructor_type(export, ctx, env, ctor_data, declars, mutual_names, d)

    # Check each recursor
    for rec_data in d.recursors:
        _check_recursor_type(export, ctx, env, rec_data, declars, mutual_names, d)


def _mutual_names(d):
    names = set()
    for ind_data in d.inductives:
        names.add(ind_data.info.name)
    for ctor_data in d.constructors:
        names.add(ctor_data.info.name)
    for rec_data in d.recursors:
        names.add(rec_data.info.name)
    return names


def _core_has_const(dag, core, names):
    """True if the (shift-ignored) core expression mentions a constant in `names`.

    Shifts don't affect constant occurrence, mirroring the Rust PR #22 walk
    over raw cores.
    """
    expr = dag.get_expr(core)
    tag = expr.tag
    if tag == 'Const':
        return expr.children[0] in names
    if tag == 'App':
        return (_core_has_const(dag, expr.children[0].core, names)
                or _core_has_const(dag, expr.children[1].core, names))
    if tag in ('Pi', 'Lambda'):
        return (_core_has_const(dag, expr.children[2].core, names)
                or _core_has_const(dag, expr.children[3].core, names))
    if tag == 'Let':
        return (_core_has_const(dag, expr.children[1].core, names)
                or _core_has_const(dag, expr.children[2].core, names)
                or _core_has_const(dag, expr.children[3].core, names))
    if tag == 'Proj':
        return _core_has_const(dag, expr.children[2].core, names)
    return False


def _computed_is_recursive(dag, ind_data, declars):
    """Recompute is_recursive by walking the constructor telescopes.

    An inductive is recursive when any constructor binder type mentions one of
    the mutual block's inductive constants.
    """
    ind_names = set(ind_data.all_inductive_infos)
    for ctor_name in ind_data.all_ctor_names:
        ctor = declars.get(ctor_name)
        if not isinstance(ctor, ConstructorDecl):
            raise ValueError(f"expected constructor declaration for {ctor_name}")
        core = ctor.data.info.ty
        while True:
            expr = dag.get_expr(core)
            if expr.tag != 'Pi':
                break
            if _core_has_const(dag, expr.children[2].core, ind_names):
                return True
            core = expr.children[3].core
    return False


def _find_last_mutual_index(declars, mutual_names):
    last_idx = -1
    for i, name in enumerate(declars):
        if name in mutual_names:
            last_idx = i
    return last_idx


def _make_tc(export, ctx, env, info):
    tc = TypeChecker(ctx, env, declar_info=info)
    return tc


def _check_inductive_type(export, ctx, env, ind_data, declars, mutual_names):
    """Check that ind_data.info.ty is a valid Sort."""
    tc = _make_tc(export, ctx, env, ind_data.info)
    tc.check_declar_info(
        _wrap_info_as_declar(ind_data.info)
    )
    # Verify the inductive's level parameters
    for lv in ctx.read_levels(ind_data.info.uparams):
        assert ctx.all_uparams_defined(lv, ind_data.info.uparams)


def _check_constructor_type(export, ctx, env, ctor_data, declars, mutual_names, d):
    """Check the constructor's type."""
    tc = _make_tc(export, ctx, env, ctor_data.info)
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
    """Verify that the constructor type is a Pi telescope ending in `ind_name`.

    Mirrors Rust ``check_ctor``'s cursor walk: peel binders with view_expr
    only. whnf must not be used here — field bodies of dependent constructors
    (e.g. `Or.inl : ∀ (a b : Prop), a → Or a b`) live at deeper OSNF frames
    and would trip the whnf shift<=depth assert.
    """
    cur = ctor_ty
    # Peel off params
    for _ in range(num_params):
        viewed = ctx.view_expr(cur)
        if viewed.tag != 'Pi':
            raise ValueError(f"constructor params exhausted for {ind_name}")
        cur = viewed.children[3]
    # Peel remaining Pi binder types (fields)
    while True:
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


def _check_recursor_type(export, ctx, env, rec_data, declars, mutual_names, d):
    """Check the recursor's type and rules."""
    tc = _make_tc(export, ctx, env, rec_data.info)
    tc.check_declar_info(
        _wrap_info_as_declar(rec_data.info)
    )
    for ind_name in rec_data.all_inductives:
        assert ind_name in declars, f"inductive {ind_name} not found for recursor"
    # Validate the recursor type structure
    rec_ty = ExprPtr.closed(rec_data.info.ty)
    _check_recursor_type_structure(tc, ctx, rec_data, rec_ty)


def _check_recursor_type_structure(tc, ctx, rec_data, rec_ty):
    """Validate the recursor's type telescope structure.

    与 _check_ctor_target_type 同理：用 view_expr 剥 binder，不 whnf——
    望远镜各层 binder 类型引用更外层的 binders（motive/minors），whnf 剥离
    依赖 OSNF 帧运气，view+peel 则对任意帧形状稳定。
    """
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
