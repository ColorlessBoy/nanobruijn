"""fol 声明语言加载器（First-Order Logic teaching declaration language）。

core.fol 是教学核心的声明库源码：启动时现场加载。语法：

    axiom <name> {u, v} : <type>
    def <name> {u} : <type> := <value>
    theorem <name> : <type> := <value>

- {u, v}：声明级 universe 参数（先插入名字，供类型/值中的 `Sort u`/`.{u}` 引用）
- 类型和值使用教学表达式语法（teaching/parser.py 的 parse_expr）
- `#` 注释；值写在 `:=` 后的缩进行（可多行续接）
"""
from __future__ import annotations

import re

from ..level import Level
from ..ptr import NamePtr
from .parser import parse_expr

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