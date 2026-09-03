from __future__ import annotations

from types import SimpleNamespace

from ...binder_style import BinderStyle
from ...env import (ConstructorData, ConstructorDecl, DeclarInfo,
                    InductiveData, InductiveDecl, RecursorData,
                    RecursorDecl, RecRule)
from ...inductive import check_inductive_declaration, core_has_const
from ...level import Level
from ...name import Name
from ...ptr import NamePtr
from ..parser import parse_expr

"""fol 片段注册表：教学核心按片段渐进加载。

每个片段是 fol 声明语言的一个 .fol 文件（声明按依赖分族）。
- make_bootstrap() 按固定顺序加载全部片段（与原 core.fol 等价）
- make_fresh_core() 不加载任何片段（游戏 --fresh 模式从零起步，
  进世界时按 .game 的 using: 字段现场定义——定义仪式）
"""

import os

_DIR = os.path.dirname(__file__)

# 片段名 → (文件, 依赖片段列表)
FRAGMENTS: dict[str, tuple[str, list[str]]] = {
    'basic': ('basic.fol', []),
    'true': ('true.fol', []),
    'false': ('false.fol', []),
    'and': ('and.fol', []),
    'or': ('or.fol', []),
    'not': ('not.fol', ['false']),
    'iff': ('iff.fol', []),
    'eq': ('eq.fol', ['iff']),
    'exists': ('exists.fol', []),
    'theorems': ('theorems.fol',
                 ['basic', 'true', 'false', 'and', 'or', 'not',
                  'iff', 'eq', 'exists']),
}

# make_bootstrap 全量加载顺序（与原 core.fol 等价）
ALL_ORDER = ['basic', 'true', 'false', 'and', 'or', 'not',
             'iff', 'eq', 'exists', 'theorems']


# 全量模式的复习表：片段 → 一句话角色
FRAGMENT_ROLES = {
    'basic': '函数组合（id / comp / flip）',
    'true': '真——唯一.intro',
    'false': '假——矛盾之源',
    'and': '合取：证据成对（ha 配 hb）',
    'or': '析取：左路或右路',
    'not': '否定：a -> False',
    'iff': '等价：两座桥（mp / mpr）',
    'eq': '等式：rewrite 的弹药',
    'exists': '存在：证人是证据',
    'theorems': '内置定理库（#print 参考）',
}


def fragment_path(name: str) -> str:
    return os.path.join(_DIR, FRAGMENTS[name][0])


def fragment_source(name: str) -> str:
    with open(fragment_path(name), encoding='utf-8') as f:
        return f.read()


def resolve_deps(names: list[str]) -> list[str]:
    """按依赖拓扑排序展开片段列表（去重，依赖在前）。"""
    out: list[str] = []

    def add(n: str) -> None:
        if n in out:
            return
        for dep in FRAGMENTS[n][1]:
            add(dep)
        out.append(n)

    for n in names:
        if n == 'all':
            for x in ALL_ORDER:
                add(x)
        else:
            if n not in FRAGMENTS:
                raise ValueError(f"fol: 未知片段 {n!r}（可选：{', '.join(FRAGMENTS)}）")
            add(n)
    return out

# ---- fol 加载器（原 teaching/fol.py）----

import re


DECL_RE = re.compile(r'^(axiom|def|theorem)\s+([\w.\'-]+)(?:\s*\{([^}]*)\})?\s*:\s*(.+)$')
IND_RE = re.compile(r'^inductive\s+([\w.\'-]+)\s*:\s*(.+)$')
CTOR_RE = re.compile(r'^ctor\s+([\w.\'-]+)\s*(?P<fields>\((?:[^()]*)\))?\s*:\s*(.+)$')
REC_RE = re.compile(r'^rec\s+([\w.\'-]+)(?:\s*\{([^}]*)\})?\s*:\s*(.+)$')
FIELD_RE = re.compile(r'\(([^()]+)\)')


def load_fol(core, path: str) -> None:
    """从 .fol 文件加载全部声明到 core.env（现场解析，失败带行号报错）。"""
    with open(path, encoding="utf-8") as f:
        lines = f.read().splitlines()
    load_fol_lines(core, lines)


def load_fol_lines(core, lines: list[str]) -> None:
    """从行列表加载 fol 声明（#def 命令与文件加载共用）。

    inductive 声明是块状（inductive 行 + 若干 ctor/rec 行），先于单行声明
    拦截处理。加载后刷新 env.cutoff（新声明视为"已确立"，可被内核查询）。"""

    decls: list[dict] = []
    cur: dict | None = None
    i = 0
    total = len(lines)
    while i < total:
        stripped = lines[i].strip()
        lineno = i + 1
        i += 1
        if not stripped or stripped.startswith('#'):
            continue
        if stripped.startswith('inductive '):
            block = [stripped]
            while i < total:
                nxt = lines[i].strip()
                if nxt.startswith('ctor ') or nxt.startswith('rec '):
                    block.append(nxt)
                    i += 1
                else:
                    break
            _build_inductive_block(core, block, lineno)
            continue
        if stripped.startswith(':=') and cur is not None:
            cur['value'] += (' ' if cur['value'] else '') + stripped[2:].strip()
            continue
        if cur is not None:
            decls.append(cur)
        m = DECL_RE.match(stripped)
        if m is None:
            raise ValueError(f"fol: 无法解析第 {lineno} 行: {stripped!r}")
        kind, name, params, ty = m.group(1), m.group(2), m.group(3), m.group(4)
        uparams = [p.strip() for p in params.split(',')] if params else []
        cur = {'kind': kind, 'name': name, 'uparams': uparams,
               'type': ty.strip(), 'value': ''}
    if cur is not None:
        decls.append(cur)

    for d in decls:
        _build_decl(core, d)
    core.env.cutoff = len(core.env.declars)


def _split_fields(s: str) -> list[tuple[str, str]]:
    """"(n : Nat) (m : Nat)" → [("n", "Nat"), ("m", "Nat")]。

    v1 限制：字段类型不含括号。"""
    out = []
    for item in FIELD_RE.findall(s or ""):
        name, _, ty = item.partition(':')
        out.append((name.strip(), ty.strip()))
    return out


def _uparam_levels(core, names: list[str]):
    """宇宙参数名 → Level 指针元组（先插入，使 parse 的 Sort u 引用同一指针）。"""
    return tuple(core.dag.insert_level(Level.param(_uparam_name(core, n)))
                 for n in names)


def _build_inductive_block(core, block: list[str], lineno: int) -> None:
    """装配 inductive/ctor/rec 块并交内核检查。

    v1 限制：无参数、无索引、Type 排序、字段类型不含括号。
    参数化/Prop 排序归纳需要 elim-level 检查机制，暂不支持。
    """
    m = IND_RE.match(block[0])
    if m is None:
        raise ValueError(f"fol: inductive 块首行无法解析（第 {lineno} 行）: {block[0]!r}")
    ind_name_str, ind_ty = m.group(1), m.group(2)
    ctor_lines = [ln for ln in block[1:] if ln.startswith('ctor ')]
    rec_lines = [ln for ln in block[1:] if ln.startswith('rec ')]
    if len(rec_lines) > 1:
        raise ValueError("fol: 一个 inductive 块最多一条 rec")
    if not ctor_lines:
        raise ValueError("fol: inductive 块至少需要一个 ctor")

    ind_ptr = core.name_to_ptr(ind_name_str)
    up_empty = core.dag.insert_uparams(())
    ind_ty_e = parse_expr(core, ind_ty)
    ind_info = DeclarInfo(name=ind_ptr, uparams=up_empty, ty=ind_ty_e.core)
    # 占位先入 env：ctor/rec 的类型里要引用归纳常量
    placeholder = InductiveDecl(info=ind_info, inductives=(), constructors=(), recursors=())
    core.env.declars[ind_ptr] = placeholder

    # 解析 ctor 行
    ctor_datas = []
    ctor_field_tys = []
    for c_line in ctor_lines:
        cm = CTOR_RE.match(c_line)
        if cm is None:
            raise ValueError(f"fol: ctor 行无法解析: {c_line!r}")
        c_name, fields_s, c_ty = cm.group(1), cm.group(2) or "", cm.group(3)
        fields = _split_fields(fields_s)
        c_ptr = core.name_to_ptr(c_name)
        ty_e = parse_expr(core, c_ty)
        for fname, fty in reversed(fields):
            ty_e = core.ctx.mk_pi(core.name_to_ptr(fname), BinderStyle.DEFAULT,
                                  parse_expr(core, fty), ty_e)
        c_info = DeclarInfo(name=c_ptr, uparams=up_empty, ty=ty_e.core)
        ctor_datas.append(ConstructorData(info=c_info, cidx=len(ctor_datas),
                                          num_params=0, num_fields=len(fields),
                                          inductive_name=ind_ptr,
                                          inductive_names=(ind_ptr,)))
        ctor_field_tys.append([parse_expr(core, fty) for _, fty in fields])

    # is_rec 从字段类型重算（内核会校验 export 标志与之一致）
    field_ptrs = [ptr for tys in ctor_field_tys for ptr in (t.core for t in tys)]
    is_rec = any(core_has_const(core.dag, ptr, {ind_ptr}) for ptr in field_ptrs)

    ind_data = InductiveData(info=ind_info, all_ctor_names=tuple(c.info.name for c in ctor_datas),
                             all_inductive_infos=(ind_ptr,), num_params=0, num_indices=0,
                             num_nested=0, is_rec=is_rec, is_reflexive=False)
    ind_decl = InductiveDecl(info=ind_info, inductives=(ind_data,),
                             constructors=tuple(ctor_datas), recursors=())
    core.env.declars[ind_ptr] = ind_decl
    for c in ctor_datas:
        core.env.declars[c.info.name] = ConstructorDecl(info=c.info, data=c)

    rec_data = None
    if rec_lines:
        rm = REC_RE.match(rec_lines[0])
        if rm is None:
            raise ValueError(f"fol: rec 行无法解析: {rec_lines[0]!r}")
        rec_name, rec_uparams_s, rec_ty = (rm.group(1), rm.group(2) or "", rm.group(3))
        rec_uparam_names = [p.strip() for p in rec_uparams_s.split(',')] if rec_uparams_s else []
        rec_up = _uparam_levels(core, rec_uparam_names)  # 先插入，parse 才能绑定 Sort u
        rec_ptr = core.name_to_ptr(rec_name)
        rec_ty_e = parse_expr(core, rec_ty)
        rec_info = DeclarInfo(name=rec_ptr,
                              uparams=core.dag.insert_uparams(rec_up),
                              ty=rec_ty_e.core)
        rules = _synthesize_rules(core, ind_ptr, rec_ptr, rec_up,
                                  ctor_datas, ctor_field_tys, rec_ty_e)
        rec_data = RecursorData(info=rec_info, num_params=0, num_indices=0,
                                num_motives=1, num_minors=len(ctor_datas),
                                rules=tuple(rules), all_inductives=(ind_ptr,), k=False)
        core.env.declars[rec_ptr] = RecursorDecl(info=rec_info, data=rec_data)
        ind_decl = InductiveDecl(info=ind_info, inductives=(ind_data,),
                                 constructors=tuple(ctor_datas), recursors=(rec_data,))
        core.env.declars[ind_ptr] = ind_decl

    export = SimpleNamespace(dag=core.dag)
    check_inductive_declaration(export, ind_decl, core.env.declars)


def _synthesize_rules(core, ind_ptr, rec_ptr, rec_up, ctor_datas, ctor_field_tys, rec_ty_e):
    """受限形状的 rec 规则综合。

    rule.val 是 λ 链，绑定顺序 [motive, minor_1..minor_k, f_1..f_n]（字段
    最内层），与内核 reduce_rec 的 foldl_apps 约定一致。body 帧中：
    f_j=Var(n-j)、minor_i=Var(n+k-i)、motive=Var(n+k)。
    递归字段（类型提到归纳常量）在字段参数后追加递归调用
    `rec motive minors... f_j`。

    λ 的 binder 类型取自解析出的 rec 望远镜前 1+k 层 + ctor 字段类型——
    归约本身不查这些类型（inst_beta 只换 body），但保持项自洽。
    """
    k = len(ctor_datas)
    rec_c = core.ctx.mk_const(rec_ptr, core.dag.insert_uparams(rec_up))

    # rec 望远镜前 1+k 层 binder 类型：motive + minors
    rec_binders = []
    cur = rec_ty_e
    for _ in range(1 + k):
        v = core.ctx.view_expr(cur)
        if v.tag != 'Pi':
            raise ValueError("fol: rec 类型望远镜层数不足（motive + minors）")
        rec_binders.append(v.children[2])
        cur = v.children[3]

    rules = []
    for i, ctor in enumerate(ctor_datas):
        n = ctor.num_fields
        field_tys = ctor_field_tys[i]
        # body 帧变量
        motive_var = core.ctx.mk_var(n + k)
        minor_var = core.ctx.mk_var(n + k - (i + 1))  # minor_{i+1}
        args = []
        for j, fty in enumerate(ctor_field_tys[i]):
            f_var = core.ctx.mk_var(n - 1 - j)
            args.append(f_var)
            if core_has_const(core.dag, fty.core, {ind_ptr}):
                rec_app = core.ctx.mk_app(rec_c, motive_var)
                for mi in range(k):
                    rec_app = core.ctx.mk_app(rec_app, core.ctx.mk_var(n + k - (mi + 1)))
                args.append(core.ctx.mk_app(rec_app, f_var))
        body = core.ctx.foldl_apps(minor_var, args)
        # λ 链：motive, minor_1..minor_k, f_1..f_n（外→内），body 最内层
        binder_types = [*rec_binders, *field_tys]
        val = body
        for bt in reversed(binder_types):
            val = core.ctx.mk_lambda(core.dag.insert_name(Name.anon()),
                                     BinderStyle.DEFAULT, bt, val)
        rules.append(RecRule(ctor_name=ctor.info.name,
                             ctor_telescope_size_wo_params=n, val=val.core))
    return rules


def _build_decl(core, d: dict) -> None:
    name: str = d['name']
    uparams: tuple[int, ...] = tuple(
        core.ctx.dag.insert_level(Level.param(_uparam_name(core, n)))
        for n in d['uparams'])
    ty = parse_expr(core, d['type'])
    _check_closed(core, ty, f"{name} 的类型")
    if d['kind'] == 'axiom':
        core._axiom(name, ty, uparams=uparams)
        return
    if not d['value']:
        raise ValueError(f"fol: {d['kind']} {name} 缺少值（:= ...）")
    val = parse_expr(core, d['value'])
    _check_closed(core, val, f"{name} 的值")
    if d['kind'] == 'def':
        core._definition(name, ty, val, uparams=uparams)
    elif d['kind'] == 'theorem':
        core._theorem(name, ty, val, uparams=uparams)
    else:  # pragma: no cover - 正则保证
        raise ValueError(f"fol: 未知声明类型 {d['kind']!r}")


def _uparam_name(core, n: str) -> NamePtr:
    """universe 参数名字（先插入，使 parse 的 Sort u/.{u} 引用同一指针）。"""
    return core.name_to_ptr(n)


def _check_closed(core, e, what: str) -> None:
    if core.ctx.dag.expr_nlbv[e.core] != 0:
        raise ValueError(f"fol: {what} 含自由变量（nlbv={core.ctx.dag.expr_nlbv[e.core]}）")