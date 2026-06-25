# Expr Tutorial Implementation Plan

**Goal:** Create `tutorials/expr/` with an HTML tutorial on `expr.py` — expression variants, ExprPtr pointers, constructors, and core operations.

**Architecture:** Three files. `style.css` copied from existing tutorial. Static HTML with 4-tab layout matching `learn_name_level/`.

**Tech Stack:** Vanilla HTML/CSS/JS.

## Global Constraints

- Same visual style (GitHub Dark) as `learn_name_level/`
- CSS copied from `learn_name_level/style.css` — no modifications
- Must work as `file://`
- Chinese language
- All code snippets from `expr.py`, `ptr.py`, `tc_context.py`

---

### Task 1: Scaffold directory + copy CSS

- [ ] Create `tutorials/expr/` directory
- [ ] Copy `style.css` from `learn_name_level/`

### Task 2: Write index.html

- [ ] Tab 1: 十种变体 — 5×2 card grid with Expr variants
- [ ] Tab 2: ExprPtr — core+shift, closed, shift_up, osnf_adj
- [ ] Tab 3: 构造器 — mk_var/app/pi/lambda/let/proj + OSNF
- [ ] Tab 4: 核心操作 — view_expr, shift, inst, unfold
- [ ] 导言 + 结语
