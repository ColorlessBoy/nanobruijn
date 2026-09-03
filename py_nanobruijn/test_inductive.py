from __future__ import annotations

from types import SimpleNamespace

import pytest

from .config import Config
from .dag import TcCtx
from .env import (
    ConstructorData,
    ConstructorDecl,
    DeclarInfo,
    Env,
    EnvLimit,
    InductiveData,
    InductiveDecl,
    RecursorData,
    RecursorDecl,
)
from .inductive import check_inductive_declaration
from .teaching.core import make_fresh_core
from .teaching.fol import fragment_source, load_fol_lines
from .name import Name
from .parser import parse_export_file
from .tc_whnf import TypeChecker


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


# ============================================================
# PR #22 alignment: Env.get_structure / infer_proj structure
# shape check / is_rec flag validation
# ============================================================


def insert_test_name(ctx: TcCtx, s: str) -> int:
    return ctx.dag.insert_name(Name.str(0, ctx.dag.insert_string(s)))


def make_ind(name, ctor_names, *, num_indices=0, is_rec=False):
    info = DeclarInfo(name=name, uparams=0, ty=0)
    return InductiveData(
        info=info,
        all_ctor_names=ctor_names,
        all_inductive_infos=(name,),
        num_params=0,
        num_indices=num_indices,
        num_nested=0,
        is_rec=is_rec,
        is_reflexive=False,
    )


def env_with(ind):
    decl = InductiveDecl(info=ind.info, inductives=(ind,), constructors=(), recursors=())
    return Env(declars={ind.info.name: decl}, limit=EnvLimit("pp_unlimited"))


def test_get_structure_shape_rules():
    # Non-recursive structure: allowed with and without rec_ok.
    ind = make_ind(1, (2,))
    env = env_with(ind)
    assert env.get_structure(1, False) is ind
    assert env.get_structure(1, True) is ind
    assert env.can_be_struct(1)

    # Recursive structure: only allowed with rec_ok=True.
    rec = make_ind(1, (2,), is_rec=True)
    env = env_with(rec)
    assert env.get_structure(1, False) is None
    assert env.get_structure(1, True) is rec
    assert not env.can_be_struct(1)

    # Multiple constructors: never a structure.
    env = env_with(make_ind(1, (2, 3)))
    assert env.get_structure(1, False) is None
    assert env.get_structure(1, True) is None

    # Indexed: never a structure.
    env = env_with(make_ind(1, (2,), num_indices=1))
    assert env.get_structure(1, False) is None
    assert env.get_structure(1, True) is None


def build_or_declars(is_rec=False, with_rec=False):
    """Build a hand-assembled `Or` inductive block.

    类型取自 fol 核心的 or 片段（与教学 REPL 同源、已由内核验证），
    这里只负责把 DeclarInfo 装配成 InductiveData / ConstructorData /
    RecursorData 结构——被测对象是内核的归纳检查逻辑本身。

    Or      : ∀ (a b : Prop), Prop          (num_params=2)
    Or.inl  : ∀ {a b : Prop}, a → Or a b    (num_fields=1)
    Or.inr  : ∀ {a b : Prop}, b → Or a b
    Or.rec  : ∀ {a b : Prop} {motive : Or a b → Prop}
              (left : ∀ (l : a), motive (@Or.inl a b l))
              (right : ∀ (r : b), motive (@Or.inr a b r))
              (t : Or a b), motive t       (望远镜 6 层)

    Returns (declars, ctx, or_name, ind_decl).
    """
    core = make_fresh_core()
    load_fol_lines(core, fragment_source("or").splitlines())
    ctx = core.ctx

    def nptr(s):
        return core.name_to_ptr(s)

    def info_of(s):
        return core.env.get_declar(nptr(s)).info

    or_name, inl_name, inr_name = nptr("Or"), nptr("Or.inl"), nptr("Or.inr")
    or_info = info_of("Or")
    ind_data = InductiveData(
        info=or_info,
        all_ctor_names=(inl_name, inr_name),
        all_inductive_infos=(or_name,),
        num_params=2,
        num_indices=0,
        num_nested=0,
        is_rec=is_rec,
        is_reflexive=False,
    )
    inl_info, inr_info = info_of("Or.inl"), info_of("Or.inr")
    inl_data = ConstructorData(
        info=inl_info, cidx=0, num_params=2, num_fields=1,
        inductive_name=or_name, inductive_names=(or_name,),
    )
    inr_data = ConstructorData(
        info=inr_info, cidx=1, num_params=2, num_fields=1,
        inductive_name=or_name, inductive_names=(or_name,),
    )

    recursors = ()
    rec_info = None
    if with_rec:
        rec_info = info_of("Or.rec")
        rec_data = RecursorData(
            info=rec_info,
            num_params=2, num_indices=0, num_motives=1, num_minors=2,
            rules=(), all_inductives=(or_name,), k=False,
        )
        recursors = (rec_data,)

    ind_decl = InductiveDecl(
        info=or_info,
        inductives=(ind_data,),
        constructors=(inl_data, inr_data),
        recursors=recursors,
    )
    declars = {
        or_name: ind_decl,
        inl_name: ConstructorDecl(info=inl_info, data=inl_data),
        inr_name: ConstructorDecl(info=inr_info, data=inr_data),
    }
    if with_rec:
        declars[nptr("Or.rec")] = RecursorDecl(info=rec_info, data=rec_data)

    return declars, ctx, or_name, ind_decl


def test_inductive_or_happy_path():
    """A correctly-flagged Or block passes the inductive checks."""
    declars, ctx, _, ind_decl = build_or_declars(is_rec=False)
    export = SimpleNamespace(dag=ctx.dag)
    check_inductive_declaration(export, ind_decl, declars)


def test_recursor_telescope_check():
    """带 Or.rec 的 Or 块通过检查：recursor 望远镜 6 层且剥离不炸帧断言。"""
    declars, ctx, _, ind_decl = build_or_declars(with_rec=True)
    export = SimpleNamespace(dag=ctx.dag)
    check_inductive_declaration(export, ind_decl, declars)


def test_recursor_telescope_count_mismatch():
    """recursor 声明的 minor 数与望远镜实际层数不符必须被拒绝。"""
    declars, ctx, _, ind_decl = build_or_declars(with_rec=True)
    rec_decl = next(d for d in declars.values() if isinstance(d, RecursorDecl))
    bad_data = RecursorData(
        info=rec_decl.data.info,
        num_params=2, num_indices=0, num_motives=1, num_minors=3,
        rules=(), all_inductives=rec_decl.data.all_inductives, k=False,
    )
    export = SimpleNamespace(dag=ctx.dag)
    # 直接走 _check_recursor_type 结构校验路径
    from .inductive import _check_recursor_type
    env = Env(declars=declars, limit=EnvLimit("by_index", len(declars)))
    with pytest.raises(ValueError, match="telescope size mismatch"):
        _check_recursor_type(export, ctx, env, bad_data, declars, set(), ind_decl)


def test_inductive_is_rec_flag_validated():
    """Wrong isRec flag (claims recursive, ctors are not) must be rejected."""
    declars, ctx, _, ind_decl = build_or_declars(is_rec=True)
    export = SimpleNamespace(dag=ctx.dag)
    with pytest.raises(ValueError, match="is_rec"):
        check_inductive_declaration(export, ind_decl, declars)


def test_infer_proj_rejects_non_structure():
    """Proj into a 2-ctor inductive must fail, not return the first ctor's field."""
    declars, ctx, or_name, _ = build_or_declars(is_rec=False)
    env = Env(declars=declars, limit=EnvLimit("pp_unlimited"))
    tc = TypeChecker(ctx, env)
    prop = ctx.mk_sort(0)
    uparams = ctx.dag.insert_uparams(())
    or_c = ctx.mk_const(or_name, uparams)
    tc.push_local(prop)  # a
    tc.push_local(prop)  # b
    or_ab = ctx.mk_app(ctx.mk_app(or_c, ctx.mk_var(1)), ctx.mk_var(0))
    tc.push_local(or_ab)  # p : Or a b
    proj = ctx.mk_proj(or_name, 0, ctx.mk_var(0))
    with pytest.raises(ValueError, match="not a structure"):
        tc.infer(proj, 'infer_only')
