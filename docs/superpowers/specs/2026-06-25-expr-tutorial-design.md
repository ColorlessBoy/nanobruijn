# Expr Tutorial Design

## Goal

Create an HTML tutorial explaining `expr.py` — the expression DAG node types,
`ExprPtr` pointer system, constructors, and core operations — following the
same style as `tutorials/learn_name_level/`.

## File Structure

```
tutorials/expr/
  index.html    — HTML content
  style.css     — reused from learn_name_level/style.css (or symlinked)
  script.js     — JS (if interactive elements needed)
```

Style copied/symlinked from the Name & Level tutorial to maintain visual
consistency. No server needed — works as `file://`.

## Content Organization

4-tab layout + 导言 + 结语.

### 导言

Brief paragraph: Expr is the core expression DAG node. After understanding
Name and Level, Expr is the next building block. It represents all kernel
expressions — variables, applications, functions, types, literals.

### Tab 1: 十种变体 (The 10 Variants)

5×2 card grid showing:

| Var(idx) | Sort(lvl) |
| Const(name, levels) | App(fun, arg) |
| Pi(name, style, type, body) | Lambda(name, style, type, body) |
| Let(name, type, val, body, nondep) | Local(name, style, type, id) |
| Proj(ty_name, idx, struct) | StringLit / NatLit |

Each card: variant name, syntax example, code constructor signature, brief
semantic description. Include the `FVarId` helper class.

### Tab 2: ExprPtr 指针系统

- core + shift pair as the fundamental handle
- `ExprPtr.closed(core)` — shift = 0xFFFF sentinel
- `shift_up(k)` — O(1) arithmetic on shift field
- `adjust_depth(from, to)` — depth-aware shift adjustment
- `osnf_adj(amount)` — OSNF normalization helper
- `is_closed()` — O(1) sentinel check
- Comparison is O(1) integer compare on (core, shift)

### Tab 3: 构造器与 OSNF 规范化

The `mk_*` constructors in `tc_context.py`:

- `mk_var(dbj_idx)` — var0-core + shift approach
- `mk_sort(lvl)` / `mk_const(name, levels)` — closed by construction
- `mk_app(fun, arg)` — min-shift normalization + osnf_adj on children
- `mk_pi` / `mk_lambda` — body_outer_shift + min-shift on type/body
- `mk_let` — three-way min-shift across type/val/body
- `mk_proj(ty_name, idx, struct)` — shift extraction from struct

### Tab 4: 核心操作

- `view_expr(ptr)` — materialize shift into actual Expr node
- `shift_expr_aux` / `shift_core_aux` — recursive shift with cutoff
- `inst(e, s, u)` / `inst_beta(e, args)` — variable substitution
- `unfold_apps` / `unfold_pi` / `unfold_lambda` — structure inspection
- `is_app` / `is_pi` / `is_lambda` — tag checks

### 结语

Expr is the heart of the expression DAG. Next step: WHNF reduction and
type inference.

## Visual Style

- Same GitHub Dark theme as existing tutorial
- Expression tree shown as indented tree (like name-tree in Name tutorial)
- Code blocks with syntax-highlighted Python
- Cards for each variant with colored badges (b-red, b-blue, etc.)
- Arrow diagrams for shift operations
- Grid-2 layout for 10 variant cards

## Constraints

- Must use same `style.css` as `learn_name_level/` — no duplicate CSS
- All interactive content must work as `file://`
- All code snippets from `expr.py` / `ptr.py` / `tc_context.py`
- Chinese language (matching existing tutorials)
