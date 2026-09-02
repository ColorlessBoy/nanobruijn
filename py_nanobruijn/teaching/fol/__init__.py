from __future__ import annotations

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

from ...level import Level
from ...ptr import NamePtr
from ..parser import parse_expr

DECL_RE = re.compile(r'^(axiom|def|theorem)\s+([\w.\'-]+)(?:\s*\{([^}]*)\})?\s*:\s*(.+)$')


def load_fol(core, path: str) -> None:
    """从 .fol 文件加载全部声明到 core.env（现场解析，失败带行号报错）。"""
    with open(path, encoding="utf-8") as f:
        lines = f.read().splitlines()

    decls: list[dict] = []
    cur: dict | None = None
    for lineno, line in enumerate(lines, 1):
        stripped = line.strip()
        if not stripped or stripped.startswith('#'):
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