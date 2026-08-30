# Teaching REPL 实现计划

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** 在 py_nanobruijn 上实现交互式教学 REPL——内置逻辑核心、Lean 风格表达式解析、逐步 β/δ 归约展示、常量查询（#check/#print/#reduce/#env）。

**Architecture:** 新增 `py_nanobruijn/teaching/` 子包（core/lexer/parser/pretty/reduce/repl），完全复用现有内核（TcCtx/TypeChecker/Env/LeanDag），内核零改动；逐步归约通过镜像 `whnf_inner` 主循环、复用 `whnf_no_unfolding`/`unfold_def` 原语实现。

**Tech Stack:** Python 3.10+（dataclass/枚举风格沿用现有代码）、pytest、ruff。

**Spec:** `docs/superpowers/specs/2026-08-30-teaching-repl-design.md`

## Global Constraints

- 内核零改动：不修改 `py_nanobruijn/tc_*.py`、`dag.py`、`env.py`、`parser.py`、`expr.py`（只能新增 teaching 子包与 `__main__.py` 的 repl 子命令）
- 测试单文件 `py_nanobruijn/test_teaching.py`（spec 规定），每个任务向其中追加测试类
- ruff：line-length 100、target py310（pyproject.toml）
- 现有 189 测试必须保持通过（`pytest py_nanobruijn -q`）
- Config：`Config(nat_extension=True, string_extension=True, unsafe_permit_all_axioms=True, unpermitted_axiom_hard_error=False)`（validate() 要求 unsafe_permit_all_axioms 与 unpermitted_axiom_hard_error 互斥）
- 教学语法 deviation（spec 澄清）：**binder 必须带类型注解**——`fun (x : A) => e`、`∀ (x : A), e`；`fun x => e` 报 ParseError（内核 Lambda 必须有 binder_type，无 metavariable）
- 内置核心 deviation（spec 澄清）：省略 `Eq.rec`/`Or.rec`/`False.rec`（类型构造复杂、入门教学价值低）；`Nat.add` 省略（需 Nat inductive，v1 不含 inductive）
- 类型错误一律 `ValueError`；超时 `CheckTimeoutError`；解析错误用 `errors.ParseError`
- LeanDag 读取 API：字符串/大整数用列表属性 `dag.strings[ptr]` / `dag.bignums[ptr]`（无 get_string/get_bignum 方法）
- de Bruijn 索引规则（Task 1 核心构造使用）：表达式位于第 k 层 binder 之下（k 从 0 计，最外层 binder 之后 k=1），binder 从内到外编号 0..n-1，`mk_var(i)` 引用第 i 个外层 binder；Pi 节点的 binder_type 处于该 binder 之外（深度 d），其 body 处于深度 d+1
- 测试 fixture 模式（来自 test_tc_infer.py）：
  ```python
  def make_ctx() -> TcCtx:
      dag = LeanDag.with_capacity(None, 0)
      return TcCtx(dag)
  def insert_name(ctx: TcCtx, s: str, pfx: int = 0) -> int:
      return ctx.dag.insert_name(Name.str(pfx, ctx.dag.insert_string(s)))
  ```
- `unfold_def` 只在常量应用处 level 参数数量与声明 uparams 数量一致时展开（tc_whnf.py:100），因此解析器对带 universe 参数的常量必须填充对应数量的 level 参数（见 Task 2）

---

### Task 1: 内置逻辑核心 teaching/core.py

**Files:**
- Create: `py_nanobruijn/teaching/__init__.py`
- Create: `py_nanobruijn/teaching/core.py`
- Test: `py_nanobruijn/test_teaching.py`（本任务创建文件并追加 TestCore 类）

**Interfaces:**
- Consumes: `LeanDag.with_capacity`、`TcCtx`、`Level`、`Name`、`BinderStyle`、`Axiom`/`Definition`/`Abbrev`/`DeclarInfo`/`Env`/`EnvLimit`、`Config`
- Produces:
  - `BootstrapCore`（`core.py`）：属性 `ctx: TcCtx`、`env: Env`、`dag: LeanDag`、`config: Config`；方法 `name_to_ptr(s: str) -> NamePtr`（点分名字，插入语义）、`name_to_string(ptr) -> str`、`make_type_checker(timeout_secs=0.0) -> TypeChecker`、`constants() -> list[str]`（排序后名字）
  - 模块级 `make_bootstrap() -> BootstrapCore`
- [ ] **Step 1: 写失败测试**

```python
# py_nanobruijn/test_teaching.py
from __future__ import annotations

import pytest

from .binder_style import BinderStyle
from .errors import ParseError
from .ptr import ExprPtr
from .teaching.core import BootstrapCore, make_bootstrap


class TestCore:
    def test_core_constants_inferable(self):
        core = make_bootstrap()
        tc = core.make_type_checker()
        for name in core.constants():
            ptr = core.name_to_ptr(name)
            info = core.env.get_declar(ptr).info
            tc.infer(ExprPtr.closed(info.ty), 'infer_only')
        # 不抛异常即通过

    def test_core_name_roundtrip(self):
        core = make_bootstrap()
        for name in core.constants():
            assert core.name_to_string(core.name_to_ptr(name)) == name

    def test_core_count(self):
        core = make_bootstrap()
        assert set(core.constants()) >= {
            "True", "True.intro", "False", "And", "And.intro", "And.left",
            "And.right", "Or", "Or.inl", "Or.inr", "Iff", "Iff.intro",
            "Iff.mp", "Iff.mpr", "Eq", "Eq.refl", "propext",
            "Not", "id", "Function.comp", "flip",
        }
```

- [ ] **Step 2: 运行确认失败**

Run: `pytest py_nanobruijn/test_teaching.py -q`
Expected: FAIL（ModuleNotFoundError: teaching）

- [ ] **Step 3: 实现 core.py**

```python
# py_nanobruijn/teaching/__init__.py
"""Teaching REPL: interactive exploration of the py_nanobruijn kernel."""
```

```python
# py_nanobruijn/teaching/core.py
from __future__ import annotations

from ..binder_style import BinderStyle
from ..config import Config
from ..dag import LeanDag, TcCtx
from ..env import Abbrev, Axiom, DeclarInfo, Definition, Env, EnvLimit
from ..level import Level
from ..name import Name
from ..ptr import ExprPtr, NamePtr
from ..tc_whnf import TypeChecker


def _name(ctx: TcCtx, s: str, pfx: int = 0) -> NamePtr:
    ptr = pfx
    for part in s.split('.'):
        ptr = ctx.dag.insert_name(Name.str(ptr, ctx.dag.insert_string(part)))
    return ptr


def _pi(ctx: TcCtx, name: str, style: BinderStyle, ty: ExprPtr, body: ExprPtr) -> ExprPtr:
    return ctx.mk_pi(_name(ctx, name), style, ty, body)


def _lam(ctx: TcCtx, name: str, style: BinderStyle, ty: ExprPtr, body: ExprPtr) -> ExprPtr:
    return ctx.mk_lambda(_name(ctx, name), style, ty, body)


def _u(ctx: TcCtx, name: str) -> tuple[NamePtr, ExprPtr]:
    u = _name(ctx, name)
    return u, ctx.mk_sort(ctx.dag.insert_level(Level.param(u)))


class BootstrapCore:
    """内置逻辑核心：用 Python 构造器直接组装 Env，仿 query_const.lean 手工定义。"""

    def __init__(self, config: Config | None = None):
        self.config = config or Config(
            nat_extension=True, string_extension=True,
            unsafe_permit_all_axioms=True, unpermitted_axiom_hard_error=False,
        )
        self.dag = LeanDag.with_capacity(self.config, 0)
        self.ctx = TcCtx(self.dag)
        self.env = Env(declars={}, limit=EnvLimit("pp_unlimited"))
        self._build()

    # ---------- 声明构造 helpers ----------

    def _axiom(self, name: str, ty: ExprPtr, uparams: tuple[NamePtr, ...] = ()) -> None:
        n = _name(self.ctx, name)
        info = DeclarInfo(name=n, uparams=self.dag.insert_uparams(uparams), ty=ty.core)
        self.env.declars[n] = Axiom(info=info, is_unsafe=False)

    def _definition(self, name: str, ty: ExprPtr, value: ExprPtr,
                    uparams: tuple[NamePtr, ...] = ()) -> None:
        n = _name(self.ctx, name)
        info = DeclarInfo(name=n, uparams=self.dag.insert_uparams(uparams), ty=ty.core)
        self.env.declars[n] = Definition(
            info=info, value=value.core, hint=Abbrev(), safety="safe",
        )

    def _const(self, name: str, uparams: tuple[NamePtr, ...]) -> ExprPtr:
        n = _name(self.ctx, name)
        return self.ctx.mk_const(n, self.dag.insert_uparams(uparams))

    # ---------- 核心构造 ----------

    def _build(self) -> None:
        ctx = self.ctx
        prop = ctx.mk_sort_zero()
        empty = ()

        # --- 逻辑 Axiom ---
        self._axiom("True", prop)
        self._axiom("True.intro", prop)
        self._axiom("False", prop)

        # And : Prop -> Prop -> Prop
        and_ty = _pi(ctx, "a", BinderStyle.DEFAULT, prop,
                     _pi(ctx, "b", BinderStyle.DEFAULT, prop, prop))
        self._axiom("And", and_ty)
        and_c = self._const("And", empty)
        # And.intro : {a} -> {b} -> a -> b -> And a b
        # binder 从内到外：hb=0, ha=1, b=2, a=3
        #   ha 的类型 a（深度2）= var2；hb 的类型 b（深度3）= var2
        #   body（深度4）= And var3 var2
        and_intro_ty = _pi(ctx, "a", BinderStyle.IMPLICIT, prop, _pi(
            ctx, "b", BinderStyle.IMPLICIT, prop, _pi(
                ctx, "ha", BinderStyle.DEFAULT, ctx.mk_var(2), _pi(
                    ctx, "hb", BinderStyle.DEFAULT, ctx.mk_var(2),
                    ctx.mk_app(ctx.mk_app(ctx.mk_app(and_c, ctx.mk_var(3)), ctx.mk_var(2)),
                               ctx.mk_var(1))))))
        self._axiom("And.intro", and_intro_ty)
        # And.left : {a} -> {b} -> And a b -> a
        # binder：h=0, b=1, a=2；h 的类型（深度2）= And var1 var0；body（深度3）= var2
        and_left_ty = _pi(ctx, "a", BinderStyle.IMPLICIT, prop, _pi(
            ctx, "b", BinderStyle.IMPLICIT, prop, _pi(
                ctx, "h", BinderStyle.DEFAULT,
                ctx.mk_app(ctx.mk_app(and_c, ctx.mk_var(1)), ctx.mk_var(0)),
                ctx.mk_var(2))))
        self._axiom("And.left", and_left_ty)
        # And.right : {a} -> {b} -> And a b -> b
        and_right_ty = _pi(ctx, "a", BinderStyle.IMPLICIT, prop, _pi(
            ctx, "b", BinderStyle.IMPLICIT, prop, _pi(
                ctx, "h", BinderStyle.DEFAULT,
                ctx.mk_app(ctx.mk_app(and_c, ctx.mk_var(1)), ctx.mk_var(0)),
                ctx.mk_var(1))))
        self._axiom("And.right", and_right_ty)

        # Or : Prop -> Prop -> Prop
        or_ty = _pi(ctx, "a", BinderStyle.DEFAULT, prop,
                    _pi(ctx, "b", BinderStyle.DEFAULT, prop, prop))
        self._axiom("Or", or_ty)
        or_c = self._const("Or", empty)
        # Or.inl : {a} -> {b} -> a -> Or a b
        # binder：h=0, b=1, a=2；h 的类型（深度2）= var1（a）；body（深度3）= Or var2 var1
        or_inl_ty = _pi(ctx, "a", BinderStyle.IMPLICIT, prop, _pi(
            ctx, "b", BinderStyle.IMPLICIT, prop, _pi(
                ctx, "h", BinderStyle.DEFAULT, ctx.mk_var(1),
                ctx.mk_app(ctx.mk_app(or_c, ctx.mk_var(2)), ctx.mk_var(1)))))
        self._axiom("Or.inl", or_inl_ty)
        # Or.inr : {a} -> {b} -> b -> Or a b
        or_inr_ty = _pi(ctx, "a", BinderStyle.IMPLICIT, prop, _pi(
            ctx, "b", BinderStyle.IMPLICIT, prop, _pi(
                ctx, "h", BinderStyle.DEFAULT, ctx.mk_var(0),
                ctx.mk_app(ctx.mk_app(or_c, ctx.mk_var(2)), ctx.mk_var(1)))))
        self._axiom("Or.inr", or_inr_ty)

        # Iff : Prop -> Prop -> Prop
        iff_ty = _pi(ctx, "a", BinderStyle.DEFAULT, prop,
                     _pi(ctx, "b", BinderStyle.DEFAULT, prop, prop))
        self._axiom("Iff", iff_ty)
        iff_c = self._const("Iff", empty)
        # Iff.intro : {a} -> {b} -> (a -> b) -> (b -> a) -> Iff a b
        # binder：mpr=0, mp=1, b=2, a=3
        #   mp 的类型（深度2）= a -> b = Pi(var1, var0)
        #   mpr 的类型（深度3）= b -> a = Pi(var2, var1)
        #   body（深度4）= Iff var3 var2
        iff_intro_ty = _pi(ctx, "a", BinderStyle.IMPLICIT, prop, _pi(
            ctx, "b", BinderStyle.IMPLICIT, prop, _pi(
                ctx, "mp", BinderStyle.DEFAULT,
                _pi(ctx, "mp0", BinderStyle.DEFAULT, ctx.mk_var(1), ctx.mk_var(0)), _pi(
                    ctx, "mpr", BinderStyle.DEFAULT,
                    _pi(ctx, "mpr0", BinderStyle.DEFAULT, ctx.mk_var(2), ctx.mk_var(1)),
                    ctx.mk_app(ctx.mk_app(iff_c, ctx.mk_var(3)), ctx.mk_var(2))))))
        self._axiom("Iff.intro", iff_intro_ty)
        # Iff.mp : {a} -> {b} -> Iff a b -> a -> b
        # binder：ha=0, h=1, b=2, a=3
        #   h 的类型（深度2）= Iff var1 var0；ha 的类型（深度3）= var2（a）；body（深度4）= var1（b）
        iff_mp_ty = _pi(ctx, "a", BinderStyle.IMPLICIT, prop, _pi(
            ctx, "b", BinderStyle.IMPLICIT, prop, _pi(
                ctx, "h", BinderStyle.DEFAULT,
                ctx.mk_app(ctx.mk_app(iff_c, ctx.mk_var(1)), ctx.mk_var(0)), _pi(
                    ctx, "ha", BinderStyle.DEFAULT, ctx.mk_var(2),
                    ctx.mk_var(1)))))
        self._axiom("Iff.mp", iff_mp_ty)
        # Iff.mpr : {a} -> {b} -> Iff a b -> b -> a
        # binder：hb=0, h=1, b=2, a=3；hb 的类型（深度3）= var1（b）；body（深度4）= var2（a）
        iff_mpr_ty = _pi(ctx, "a", BinderStyle.IMPLICIT, prop, _pi(
            ctx, "b", BinderStyle.IMPLICIT, prop, _pi(
                ctx, "h", BinderStyle.DEFAULT,
                ctx.mk_app(ctx.mk_app(iff_c, ctx.mk_var(1)), ctx.mk_var(0)), _pi(
                    ctx, "hb", BinderStyle.DEFAULT, ctx.mk_var(1),
                    ctx.mk_var(2)))))
        self._axiom("Iff.mpr", iff_mpr_ty)

        # Eq : {α : Sort u} -> α -> α -> Prop
        u, su = _u(ctx, "u")
        eq_ty = _pi(ctx, "α", BinderStyle.IMPLICIT, su, _pi(
            ctx, "a1", BinderStyle.DEFAULT, ctx.mk_var(0), _pi(
                ctx, "a2", BinderStyle.DEFAULT, ctx.mk_var(0), prop)))
        self._axiom("Eq", eq_ty, uparams=(u,))
        eq_c = self._const("Eq", (u,))
        # Eq.refl : {α : Sort u} -> (a : α) -> Eq α a a
        # binder：a=0, α=1；a 的类型（深度1）= var0（α）；body（深度2）= Eq var1 var0 var0
        eq_refl_ty = _pi(ctx, "α", BinderStyle.IMPLICIT, su, _pi(
            ctx, "a", BinderStyle.DEFAULT, ctx.mk_var(0),
            ctx.mk_app(ctx.mk_app(ctx.mk_app(eq_c, ctx.mk_var(1)), ctx.mk_var(0)),
                       ctx.mk_var(0))))
        self._axiom("Eq.refl", eq_refl_ty, uparams=(u,))

        # propext : {a : Prop} -> {b : Prop} -> Iff a b -> Eq Prop a b
        # binder：h=0, b=1, a=2；h 的类型（深度2）= Iff var1 var0
        # body（深度3）= Eq Prop var2 var1（Prop 是闭式，直接插入）
        propext_ty = _pi(ctx, "a", BinderStyle.IMPLICIT, prop, _pi(
            ctx, "b", BinderStyle.IMPLICIT, prop, _pi(
                ctx, "h", BinderStyle.DEFAULT,
                ctx.mk_app(ctx.mk_app(iff_c, ctx.mk_var(1)), ctx.mk_var(0)),
                ctx.mk_app(ctx.mk_app(ctx.mk_app(eq_c, prop), ctx.mk_var(2)), ctx.mk_var(1)))))
        self._axiom("propext", propext_ty)

        # --- Definition（可 δ 展开）---
        # Not : Prop -> Prop，value = fun (a : Prop) => a -> False
        not_ty = _pi(ctx, "a", BinderStyle.DEFAULT, prop, prop)
        not_val = _lam(ctx, "a", BinderStyle.DEFAULT, prop,
                       _pi(ctx, "n", BinderStyle.DEFAULT, ctx.mk_var(0), prop))
        self._definition("Not", not_ty, not_val)

        # id : {α : Sort u} -> α -> α，value = fun {α} (a : α) => a
        u2, su2 = _u(ctx, "u")
        id_ty = _pi(ctx, "α", BinderStyle.IMPLICIT, su2, _pi(
            ctx, "a", BinderStyle.DEFAULT, ctx.mk_var(0), ctx.mk_var(0)))
        id_val = _lam(ctx, "α", BinderStyle.IMPLICIT, su2, _lam(
            ctx, "a", BinderStyle.DEFAULT, ctx.mk_var(0), ctx.mk_var(0)))
        self._definition("id", id_ty, id_val, uparams=(u2,))

        # Function.comp : {α : Sort u} -> {β : Sort v} -> {δ : Sort w} ->
        #                 (β -> δ) -> (α -> β) -> α -> δ
        # binder 从内到外：x=0, g=1, f=2, δ=3, β=4, α=5
        #   f 的类型（深度3）= β -> δ = Pi(var2, var1)
        #   g 的类型（深度4）= α -> β = Pi(var4, var3)
        #   x 的类型（深度5）= var5（α）；body（深度6）= f (g x) = App(var2, App(var1, var0))
        u3, su3 = _u(ctx, "u")
        v3, sv3 = _u(ctx, "v")
        w3, sw3 = _u(ctx, "w")
        comp_body = ctx.mk_app(ctx.mk_var(2), ctx.mk_app(ctx.mk_var(1), ctx.mk_var(0)))
        comp_ty = _pi(ctx, "α", BinderStyle.IMPLICIT, su3, _pi(
            ctx, "β", BinderStyle.IMPLICIT, sv3, _pi(
                ctx, "δ", BinderStyle.IMPLICIT, sw3, _pi(
                    ctx, "f", BinderStyle.DEFAULT,
                    _pi(ctx, "f0", BinderStyle.DEFAULT, ctx.mk_var(2), ctx.mk_var(1)), _pi(
                        ctx, "g", BinderStyle.DEFAULT,
                        _pi(ctx, "g0", BinderStyle.DEFAULT, ctx.mk_var(4), ctx.mk_var(3)), _pi(
                            ctx, "x", BinderStyle.DEFAULT, ctx.mk_var(5), comp_body))))))
        comp_val = _lam(ctx, "α", BinderStyle.IMPLICIT, su3, _lam(
            ctx, "β", BinderStyle.IMPLICIT, sv3, _lam(
                ctx, "δ", BinderStyle.IMPLICIT, sw3, _lam(
                    ctx, "f", BinderStyle.DEFAULT,
                    _pi(ctx, "f0", BinderStyle.DEFAULT, ctx.mk_var(2), ctx.mk_var(1)), _lam(
                        ctx, "g", BinderStyle.DEFAULT,
                        _pi(ctx, "g0", BinderStyle.DEFAULT, ctx.mk_var(4), ctx.mk_var(3)), _lam(
                            ctx, "x", BinderStyle.DEFAULT, ctx.mk_var(5),
                            ctx.mk_app(ctx.mk_var(2), ctx.mk_app(ctx.mk_var(1), ctx.mk_var(0)))))))))
        self._definition("Function.comp", comp_ty, comp_val,
                         uparams=(u3, v3, w3))

        # flip : {α : Sort u} -> {β : Sort v} -> {φ : Sort w} ->
        #        (α -> β -> φ) -> β -> α -> φ
        # binder 从内到外：a=0, b=1, f=2, φ=3, β=4, α=5
        #   f 的类型（深度3）= α -> β -> φ = Pi(var3, Pi(var2, var1))
        #   b 的类型（深度4）= var3（β）；a 的类型（深度5）= var4（α）
        #   body（深度6）= f a b = App(App(var2, var0), var1)
        u4, su4 = _u(ctx, "u")
        v4, sv4 = _u(ctx, "v")
        w4, sw4 = _u(ctx, "w")
        flip_body = ctx.mk_app(ctx.mk_app(ctx.mk_var(2), ctx.mk_var(0)), ctx.mk_var(1))
        flip_ty = _pi(ctx, "α", BinderStyle.IMPLICIT, su4, _pi(
            ctx, "β", BinderStyle.IMPLICIT, sv4, _pi(
                ctx, "φ", BinderStyle.IMPLICIT, sw4, _pi(
                    ctx, "f", BinderStyle.DEFAULT,
                    _pi(ctx, "f0", BinderStyle.DEFAULT, ctx.mk_var(3),
                        _pi(ctx, "f1", BinderStyle.DEFAULT, ctx.mk_var(2), ctx.mk_var(1))), _pi(
                        ctx, "b", BinderStyle.DEFAULT, ctx.mk_var(3), _pi(
                            ctx, "a", BinderStyle.DEFAULT, ctx.mk_var(4), flip_body))))))
        flip_val = _lam(ctx, "α", BinderStyle.IMPLICIT, su4, _lam(
            ctx, "β", BinderStyle.IMPLICIT, sv4, _lam(
                ctx, "φ", BinderStyle.IMPLICIT, sw4, _lam(
                    ctx, "f", BinderStyle.DEFAULT,
                    _pi(ctx, "f0", BinderStyle.DEFAULT, ctx.mk_var(3),
                        _pi(ctx, "f1", BinderStyle.DEFAULT, ctx.mk_var(2), ctx.mk_var(1))), _lam(
                        ctx, "b", BinderStyle.DEFAULT, ctx.mk_var(3), _lam(
                            ctx, "a", BinderStyle.DEFAULT, ctx.mk_var(4),
                            ctx.mk_app(ctx.mk_app(ctx.mk_var(2), ctx.mk_var(0)),
                                       ctx.mk_var(1))))))))
        self._definition("flip", flip_ty, flip_val, uparams=(u4, v4, w4))

    # ---------- 公开 API ----------

    def name_to_ptr(self, s: str) -> NamePtr:
        return _name(self.ctx, s)

    def name_to_string(self, ptr: NamePtr) -> str:
        return self.ctx.name_to_string(ptr)

    def constants(self) -> list[str]:
        return sorted(self.name_to_string(n) for n in self.env.declars)

    def make_type_checker(self, timeout_secs: float = 0.0) -> TypeChecker:
        return TypeChecker(self.ctx, self.env, timeout_secs=timeout_secs)


def make_bootstrap() -> BootstrapCore:
    return BootstrapCore()
```

- [ ] **Step 4: 运行测试**

Run: `pytest py_nanobruijn/test_teaching.py -q`
Expected: PASS（3 个 TestCore 测试）。若 `test_core_constants_inferable` 报索引错误，按代码注释中的 binder 编号核对 `mk_var` 参数。

- [ ] **Step 5: 提交**

```bash
git add py_nanobruijn/teaching py_nanobruijn/test_teaching.py
git commit -m "feat(teaching): bootstrap logic core with Prop-logic constants"
```

---

### Task 2: 表达式解析器 teaching/lexer.py + teaching/parser.py

**Files:**
- Create: `py_nanobruijn/teaching/lexer.py`
- Create: `py_nanobruijn/teaching/parser.py`
- Test: `py_nanobruijn/test_teaching.py`（追加 TestParser 类）

**Interfaces:**
- Consumes: `BootstrapCore`（Task 1）、`errors.ParseError`、`BinderStyle`、`Name`、`Level`
- Produces:
  - `lexer.py`: `tokenize(text: str) -> list[tuple[str, object]]`（`(kind, value)`；kind ∈ `name`/`kw`/`sym`/`int`；name 为点分字符串，sym 为 `(`,`)`,`:`,`,`,`@`,`=>`,`->`,`∀`，int 为 int）
  - `parser.py`: `parse_expr(core: BootstrapCore, text: str) -> ExprPtr`；错误抛 `ParseError`
  - 语法：`(e)`、`@name`、`fun (x : A) => e`、`fun {x : A} => e`、`∀ (x : A), e`、`forall (x : A), e`、`A -> B`、`Type`、`Prop`、`Type u`/`Sort u`、自然数、点分常量名、空格应用
  - 常量带 universe 参数时自动填充 `u0/u1/...` 显式层级参数（否则 `unfold_def` 不展开，且 kernel 层 Const 应用需要 level 参数）
  - 未绑定标识符 → `ParseError`；`fun x => e`（无类型 binder）→ `ParseError`

- [ ] **Step 1: 写失败测试**（追加到 test_teaching.py，import 更新为：`from .teaching.parser import parse_expr`、`from .level import Level`、`from .name import Name`）

```python
class TestParser:
    def test_parse_var(self):
        core = make_bootstrap()
        e = parse_expr(core, "fun (x : Prop) => x")
        v = core.ctx.view_expr(e)
        assert v.tag == 'Lambda'
        assert core.ctx.view_expr(v.body).tag == 'Var'

    def test_parse_const_app(self):
        core = make_bootstrap()
        e = parse_expr(core, "And.intro True.intro True.intro")
        v = core.ctx.view_expr(e)
        assert v.tag == 'App'
        fun_v = core.ctx.view_expr(v.fun)
        assert fun_v.tag == 'Const'

    def test_parse_at_explicit(self):
        core = make_bootstrap()
        e = parse_expr(core, "@And True True")
        v = core.ctx.view_expr(e)
        assert v.tag == 'App'

    def test_parse_pi_arrow(self):
        core = make_bootstrap()
        e = parse_expr(core, "Prop -> Prop")
        v = core.ctx.view_expr(e)
        assert v.tag == 'Pi'

    def test_parse_implicit_binder(self):
        core = make_bootstrap()
        e = parse_expr(core, "fun {x : Prop} => x")
        v = core.ctx.view_expr(e)
        assert v.tag == 'Lambda'
        assert v.binder_style == BinderStyle.IMPLICIT

    def test_parse_nat_lit(self):
        core = make_bootstrap()
        e = parse_expr(core, "42")
        assert core.ctx.view_expr(e).tag == 'NatLit'

    def test_parse_unbound_var_raises(self):
        core = make_bootstrap()
        with pytest.raises(ParseError):
            parse_expr(core, "x")

    def test_parse_fun_without_type_raises(self):
        core = make_bootstrap()
        with pytest.raises(ParseError):
            parse_expr(core, "fun x => x")

    def test_parse_unbalanced_paren_raises(self):
        core = make_bootstrap()
        with pytest.raises(ParseError):
            parse_expr(core, "(fun (x : Prop) => x")

    def test_parse_unknown_const_raises(self):
        core = make_bootstrap()
        with pytest.raises(ParseError):
            parse_expr(core, "NoSuchConst")
```

- [ ] **Step 2: 运行确认失败**

Run: `pytest py_nanobruijn/test_teaching.py::TestParser -q`
Expected: FAIL（ModuleNotFoundError: teaching.parser）

- [ ] **Step 3: 实现 lexer.py**

```python
# py_nanobruijn/teaching/lexer.py
from __future__ import annotations

from ..errors import ParseError

KEYWORDS = {"fun", "forall", "Type", "Prop", "Sort"}
SYMBOLS = set("():,@=>∀")

Token = tuple[str, object]


def tokenize(text: str) -> list[Token]:
    tokens: list[Token] = []
    i = 0
    n = len(text)
    while i < n:
        c = text[i]
        if c.isspace():
            i += 1
            continue
        if c.isdigit():
            j = i
            while j < n and text[j].isdigit():
                j += 1
            tokens.append(("int", int(text[i:j])))
            i = j
            continue
        if c == '-':
            if i + 1 < n and text[i + 1] == '>':
                tokens.append(("sym", "->"))
                i += 2
                continue
            raise ParseError(f"unexpected character {c!r} at position {i}")
        if c == '=':
            if i + 1 < n and text[i + 1] == '>':
                tokens.append(("sym", "=>"))
                i += 2
                continue
            raise ParseError(f"unexpected character {c!r} at position {i}")
        if c == '∀':
            tokens.append(("sym", "∀"))
            i += 1
            continue
        if c in SYMBOLS:
            tokens.append(("sym", c))
            i += 1
            continue
        if c.isalpha() or c == '_':
            j = i
            while j < n and (text[j].isalnum() or text[j] in "._'"):
                j += 1
            word = text[i:j]
            if word in KEYWORDS:
                tokens.append(("kw", word))
            else:
                tokens.append(("name", word))
            i = j
            continue
        raise ParseError(f"unexpected character {c!r} at position {i}")
    return tokens
```

- [ ] **Step 4: 实现 parser.py**

```python
# py_nanobruijn/teaching/parser.py
from __future__ import annotations

from ..binder_style import BinderStyle
from ..errors import ParseError
from ..level import Level
from ..name import Name
from ..ptr import ExprPtr, NamePtr
from .core import BootstrapCore
from .lexer import tokenize


def parse_expr(core: BootstrapCore, text: str) -> ExprPtr:
    return _ExprParser(core, text).parse()


class _ExprParser:
    def __init__(self, core: BootstrapCore, text: str):
        self.core = core
        self.ctx = core.ctx
        self.tokens = tokenize(text)
        self.pos = 0
        self.binders: list[str] = []

    # ---------- token 工具 ----------

    def peek(self) -> tuple[str, object] | None:
        return self.tokens[self.pos] if self.pos < len(self.tokens) else None

    def advance(self) -> tuple[str, object]:
        tok = self.peek()
        if tok is None:
            raise ParseError("unexpected end of input")
        self.pos += 1
        return tok

    def is_sym(self, s: str) -> bool:
        tok = self.peek()
        return tok is not None and tok[0] == "sym" and tok[1] == s

    def expect_sym(self, s: str) -> None:
        if not self.is_sym(s):
            raise ParseError(f"expected {s!r}, got {self.peek()!r}")
        self.advance()

    # ---------- 语法 ----------

    def parse(self) -> ExprPtr:
        e = self.parse_arrow()
        if self.peek() is not None:
            raise ParseError(f"unexpected trailing input {self.peek()!r}")
        return e

    def parse_arrow(self) -> ExprPtr:
        left = self.parse_app()
        if self.is_sym("->"):
            self.advance()
            right = self.parse_arrow()
            anon = self.ctx.dag.insert_name(Name.anon())
            return self.ctx.mk_pi(anon, BinderStyle.DEFAULT, left, right)
        return left

    def parse_app(self) -> ExprPtr:
        head = self.parse_atom()
        while self._starts_atom():
            head = self.ctx.mk_app(head, self.parse_atom())
        return head

    def _starts_atom(self) -> bool:
        tok = self.peek()
        if tok is None:
            return False
        kind, value = tok
        if kind == "int" or kind == "name":
            return True
        if kind == "kw":
            return value in {"fun", "forall", "Type", "Prop", "Sort"}
        if kind == "sym":
            return value in {"(", "@", "∀"}
        return False

    def parse_atom(self) -> ExprPtr:
        tok = self.peek()
        if tok is None:
            raise ParseError("expected expression, got end of input")
        kind, value = tok
        if kind == "int":
            self.advance()
            return self.ctx.mk_nat_lit(value)
        if kind == "sym" and value == "(":
            self.advance()
            e = self.parse_arrow()
            self.expect_sym(")")
            return e
        if kind == "sym" and value == "@":
            self.advance()
            n = self.advance()
            if n[0] != "name":
                raise ParseError("expected constant name after '@'")
            return self._const_or_bound(n[1], explicit=True)
        if kind == "kw" and value == "fun":
            return self.parse_fun()
        if kind in ("sym", "kw") and value in ("∀", "forall"):
            return self.parse_pi()
        if kind == "kw" and value == "Prop":
            self.advance()
            return self.ctx.mk_sort(0)
        if kind == "kw" and value == "Type":
            self.advance()
            return self._parse_type()
        if kind == "kw" and value == "Sort":
            self.advance()
            return self._parse_type()
        if kind == "name":
            self.advance()
            return self._const_or_bound(value, explicit=False)
        raise ParseError(f"unexpected token {tok!r}")

    def _parse_type(self) -> ExprPtr:
        tok = self.peek()
        if tok is not None and tok[0] == "name":
            self.advance()
            n = self.ctx.dag.insert_name(Name.str(0, self.ctx.dag.insert_string(tok[1])))
            return self.ctx.mk_sort(self.ctx.dag.insert_level(Level.param(n)))
        return self.ctx.mk_sort(1)

    def _const_or_bound(self, dotted: str, explicit: bool) -> ExprPtr:
        if not explicit and "." not in dotted:
            idx = self._bound_index(dotted)
            if idx is not None:
                return self.ctx.mk_var(idx)
        ptr = self.core.name_to_ptr(dotted)
        decl = self.core.env.declars.get(ptr)
        if decl is not None:
            uparams = self.core.dag.uparams[decl.info.uparams]
            if uparams:
                levels = tuple(
                    self.ctx.dag.insert_level(Level.param(self.core.name_to_ptr(f"u{i}")))
                    for i in range(len(uparams)))
                return self.ctx.mk_const(ptr, self.ctx.dag.insert_uparams(levels))
            return self.ctx.mk_const(ptr, self.ctx.dag.insert_uparams(()))
        if not explicit and "." not in dotted:
            raise ParseError(
                f"unknown identifier {dotted!r}: not a bound variable "
                f"(try `fun ({dotted} : A) => ...`) nor a declared constant"
            )
        raise ParseError(f"unknown constant {dotted!r}")

    def _bound_index(self, name: str) -> int | None:
        for i, b in enumerate(reversed(self.binders)):
            if b == name:
                return i
        return None

    # ---------- binder 语法 ----------

    def parse_fun(self) -> ExprPtr:
        self.advance()  # 'fun'
        binder = self._parse_binder()
        self.expect_sym("=>")
        self.binders.append(binder[0])
        try:
            body = self.parse_arrow()
        finally:
            self.binders.pop()
        return self.ctx.mk_lambda(
            self.core.name_to_ptr(binder[0]), binder[1], binder[2], body)

    def parse_pi(self) -> ExprPtr:
        self.advance()  # '∀' / 'forall'
        binder = self._parse_binder()
        self.expect_sym(",")
        self.binders.append(binder[0])
        try:
            body = self.parse_arrow()
        finally:
            self.binders.pop()
        return self.ctx.mk_pi(
            self.core.name_to_ptr(binder[0]), binder[1], binder[2], body)

    def _parse_binder(self) -> tuple[str, BinderStyle, ExprPtr]:
        tok = self.advance()
        if tok[0] != "sym" or tok[1] not in ("(", "{"):
            raise ParseError(
                f"binder must be annotated with a type, e.g. `fun (x : A) => ...`; "
                f"got {tok!r}"
            )
        style = BinderStyle.IMPLICIT if tok[1] == "{" else BinderStyle.DEFAULT
        close = "}" if tok[1] == "{" else ")"
        name_tok = self.advance()
        if name_tok[0] != "name":
            raise ParseError("expected binder name")
        self.expect_sym(":")
        ty = self.parse_arrow()
        self.expect_sym(close)
        return name_tok[1], style, ty
```

要点：
- binder 类型在 push 名字**之前**解析（`_parse_binder` 不 push，`parse_fun`/`parse_pi` 在解析 body 前 push、`finally` 中 pop），保证嵌套 binder 的变量索引正确
- `_const_or_bound` 对声明了 universe 参数的常量（id/Function.comp/flip/Eq/Eq.refl）填充 `u0/u1/...` 显式层级参数，使 `unfold_def` 的 level 数量检查通过（tc_whnf.py:100）

- [ ] **Step 5: 运行测试**

Run: `pytest py_nanobruijn/test_teaching.py::TestParser -q`
Expected: PASS

- [ ] **Step 6: 提交**

```bash
git add py_nanobruijn/teaching/lexer.py py_nanobruijn/teaching/parser.py py_nanobruijn/test_teaching.py
git commit -m "feat(teaching): Lean-style expression parser (fun/forall/app/@/Type)"
```

---

### Task 3: pretty printer teaching/pretty.py

**Files:**
- Create: `py_nanobruijn/teaching/pretty.py`
- Test: `py_nanobruijn/test_teaching.py`（追加 TestPretty 类）

**Interfaces:**
- Consumes: `BootstrapCore`、`parse_expr`（Task 2）
- Produces: `pretty(core: BootstrapCore, e: ExprPtr) -> str`；内部 `_Pretty` 类方法 `_pp(e, names)`、`_has_free0(e, depth)`（判断 de Bruijn 索引 depth 是否自由出现，用于 `->` 简写）

- [ ] **Step 1: 写失败测试**（追加 import：`from .teaching.pretty import pretty`）

```python
class TestPretty:
    def test_pretty_var(self):
        core = make_bootstrap()
        e = parse_expr(core, "fun (x : Prop) => x")
        assert pretty(core, e) == "fun (x : Prop) => x"

    def test_pretty_arrow_shortcut(self):
        core = make_bootstrap()
        e = parse_expr(core, "Prop -> Prop")
        assert pretty(core, e) == "Prop -> Prop"

    def test_pretty_pi_forall(self):
        core = make_bootstrap()
        e = parse_expr(core, "∀ (a : Prop), a -> Prop")
        assert pretty(core, e) == "∀ (a : Prop), a -> Prop"

    def test_pretty_const_app(self):
        core = make_bootstrap()
        e = parse_expr(core, "@And True True")
        assert pretty(core, e) == "@And True True"

    def test_pretty_nat_lit(self):
        core = make_bootstrap()
        e = parse_expr(core, "42")
        assert pretty(core, e) == "42"

    def test_pretty_implicit_binder(self):
        core = make_bootstrap()
        e = parse_expr(core, "fun {x : Prop} => x")
        assert pretty(core, e) == "fun {x : Prop} => x"

    def test_pretty_const(self):
        core = make_bootstrap()
        e = parse_expr(core, "And.intro")
        assert pretty(core, e) == "And.intro"
```

- [ ] **Step 2: 运行确认失败**

Run: `pytest py_nanobruijn/test_teaching.py::TestPretty -q`
Expected: FAIL（ModuleNotFoundError: teaching.pretty）

- [ ] **Step 3: 实现 pretty.py**

```python
# py_nanobruijn/teaching/pretty.py
from __future__ import annotations

from ..binder_style import BinderStyle
from ..ptr import ExprPtr
from .core import BootstrapCore


def pretty(core: BootstrapCore, e: ExprPtr) -> str:
    return _Pretty(core)._pp(e, ())


class _Pretty:
    def __init__(self, core: BootstrapCore):
        self.core = core
        self.ctx = core.ctx

    def _pp(self, e: ExprPtr, names: tuple[str, ...]) -> str:
        v = self.ctx.view_expr(e)
        tag = v.tag
        if tag == 'Var':
            idx = v.dbj_idx
            if idx < len(names):
                return names[-1 - idx]
            return f"#{idx}"
        if tag == 'Sort':
            return self._pp_sort(v.level)
        if tag == 'Const':
            return self.ctx.name_to_string(v.name)
        if tag == 'App':
            fun_v = self.ctx.view_expr(v.fun)
            if fun_v.tag == 'Const' and self._const_is_implicit_first(v):
                return f"@{self.ctx.name_to_string(fun_v.name)} {self._pp(v.arg, names)}"
            return f"{self._pp(v.fun, names)} {self._pp(v.arg, names)}"
        if tag == 'Pi':
            return self._pp_binder(v.binder_name, v.binder_style, v.binder_type, v.body,
                                   names, is_lambda=False)
        if tag == 'Lambda':
            return self._pp_binder(v.binder_name, v.binder_style, v.binder_type, v.body,
                                   names, is_lambda=True)
        if tag == 'Let':
            n = self.ctx.name_to_string(v.binder_name)
            return f"let {n} := {self._pp(v.val, names)}; {self._pp(v.body, names + (n,))}"
        if tag == 'Proj':
            return f"{self.ctx.name_to_string(v.ty_name)}.{v.proj_idx} {self._pp(v.structure, names)}"
        if tag == 'StringLit':
            return f'"{self.ctx.dag.strings[v.string_ptr]}"'
        if tag == 'NatLit':
            return str(self.ctx.dag.bignums[v.nat_ptr])
        return f"<{tag}>"

    def _pp_sort(self, level_ptr) -> str:
        lv = self.ctx.dag.get_level(level_ptr)
        if lv.is_zero():
            return "Prop"
        if lv.tag == 'Succ' and self.ctx.dag.get_level(lv.pred).is_zero():
            return "Type"
        return f"Type {self.ctx.name_to_string(lv.param_name)}"

    def _const_is_implicit_first(self, v) -> bool:
        info = self.core.env.get_declar(v.name).info
        ty_v = self.ctx.view_expr(ExprPtr.closed(info.ty))
        if ty_v.tag == 'Pi':
            return ty_v.binder_style == BinderStyle.IMPLICIT
        return False

    def _pp_binder(self, name_ptr, style, binder_type, body, names, *, is_lambda):
        name = self.ctx.name_to_string(name_ptr)
        head = "fun" if is_lambda else "∀"
        open_b, close_b = ("{", "}") if style == BinderStyle.IMPLICIT else ("(", ")")
        body_names = names + (name,)
        if not is_lambda and not self._has_free0(body, 1):
            return f"{self._pp(binder_type, names)} -> {self._pp(body, body_names)}"
        return f"{head} {open_b}{name} : {self._pp(binder_type, names)}{close_b}, {self._pp(body, body_names)}"

    def _has_free0(self, e: ExprPtr, depth: int) -> bool:
        """判断 de Bruijn 索引 depth 是否自由出现在 e 中（view 已合成 shift）。"""
        v = self.ctx.view_expr(e)
        tag = v.tag
        if tag == 'Var':
            return v.dbj_idx == depth
        if tag in ('Const', 'Sort', 'StringLit', 'NatLit'):
            return False
        if tag == 'App':
            return self._has_free0(v.fun, depth) or self._has_free0(v.arg, depth)
        if tag in ('Pi', 'Lambda'):
            return (self._has_free0(v.binder_type, depth) or
                    self._has_free0(v.body, depth + 1))
        if tag == 'Let':
            return (self._has_free0(v.binder_type, depth) or
                    self._has_free0(v.val, depth) or
                    self._has_free0(v.body, depth + 1))
        if tag == 'Proj':
            return self._has_free0(v.structure, depth)
        return False
```

要点：
- `->` 简写：Pi 的 body 不引用新 binder（`_has_free0(body, 1)` 为 False）时打印 `A -> B`
- 隐式 binder 打印 `{x : A}`（与 parser 语法一致，往返成立）
- `@` 前缀：常量类型首 binder 为 IMPLICIT 时打印 `@Const ...`
- `dag.strings`/`dag.bignums` 是列表属性（无 get 方法）

- [ ] **Step 4: 运行测试**

Run: `pytest py_nanobruijn/test_teaching.py::TestPretty -q`
Expected: PASS

- [ ] **Step 5: 追加往返测试**

```python
    def test_pretty_parse_roundtrip(self):
        core = make_bootstrap()
        for text in [
            "fun (x : Prop) => x",
            "Prop -> Prop",
            "∀ (a : Prop), a -> Prop",
            "@And True True",
            "@And.intro True.intro True.intro",
            "fun {x : Prop} => x",
            "42",
            "id",
        ]:
            assert pretty(core, parse_expr(core, text)) == text
```

- [ ] **Step 6: 运行全量测试**

Run: `pytest py_nanobruijn/test_teaching.py -q`
Expected: PASS（TestCore + TestParser + TestPretty）

- [ ] **Step 7: 提交**

```bash
git add py_nanobruijn/teaching/pretty.py py_nanobruijn/test_teaching.py
git commit -m "feat(teaching): pretty printer for ExprPtr -> Lean syntax"
```

---

### Task 4: 逐步归约 teaching/reduce.py

**Files:**
- Create: `py_nanobruijn/teaching/reduce.py`
- Test: `py_nanobruijn/test_teaching.py`（追加 TestReduce 类）

**Interfaces:**
- Consumes: `BootstrapCore`、`parse_expr`、`pretty`、`TypeChecker`（`whnf_no_unfolding`/`unfold_def`）
- Produces:
  - `ReductionStep`（NamedTuple）：`before: ExprPtr`、`after: ExprPtr`、`kind: str`（`'beta'`/`'delta'`）
  - `reduce_steps(tc: TypeChecker, e: ExprPtr) -> list[ReductionStep]`：镜像 `whnf_inner` 主循环；`unfold_def` 成功记 `'delta'`，`whnf_no_unfolding` 有变化记 `'beta'`，无变化终止
  - `show_reduction(core: BootstrapCore, steps: list[ReductionStep]) -> str`

- [ ] **Step 1: 写失败测试**（追加 import：`from .teaching.reduce import ReductionStep, reduce_steps, show_reduction`）

```python
class TestReduce:
    def test_beta_reduction_steps(self):
        core = make_bootstrap()
        tc = core.make_type_checker()
        e = parse_expr(core, "(fun (x : Prop) => x) True.intro")
        steps = reduce_steps(tc, e)
        assert [s.kind for s in steps] == ["beta"]
        assert pretty(core, steps[-1].after) == "True.intro"

    def test_delta_reduction_steps(self):
        core = make_bootstrap()
        tc = core.make_type_checker()
        # id True.intro：先 δ 展开 id（α := True），再 β 归约
        e = parse_expr(core, "id True.intro")
        steps = reduce_steps(tc, e)
        assert [s.kind for s in steps] == ["delta", "beta"]
        assert pretty(core, steps[-1].after) == "True.intro"

    def test_whnf_term_no_steps(self):
        core = make_bootstrap()
        tc = core.make_type_checker()
        e = parse_expr(core, "True.intro")
        assert reduce_steps(tc, e) == []

    def test_show_reduction_format(self):
        core = make_bootstrap()
        tc = core.make_type_checker()
        e = parse_expr(core, "(fun (x : Prop) => x) True.intro")
        out = show_reduction(core, reduce_steps(tc, e))
        assert "(fun (x : Prop) => x) True.intro" in out
        assert "True.intro" in out
        assert "[beta]" in out
```

- [ ] **Step 2: 运行确认失败**

Run: `pytest py_nanobruijn/test_teaching.py::TestReduce -q`
Expected: FAIL（ModuleNotFoundError: teaching.reduce）

- [ ] **Step 3: 实现 reduce.py**

```python
# py_nanobruijn/teaching/reduce.py
from __future__ import annotations

from typing import NamedTuple

from ..ptr import ExprPtr
from ..tc_whnf import TypeChecker
from .core import BootstrapCore
from .pretty import pretty


class ReductionStep(NamedTuple):
    before: ExprPtr
    after: ExprPtr
    kind: str  # 'beta' | 'delta'


def reduce_steps(tc: TypeChecker, e: ExprPtr) -> list[ReductionStep]:
    steps: list[ReductionStep] = []
    cursor = e
    while True:
        r = tc.whnf_no_unfolding(cursor)
        unfolded = tc.unfold_def(r)
        if unfolded is not None:
            steps.append(ReductionStep(cursor, unfolded, "delta"))
            cursor = unfolded
            continue
        if r != cursor:
            steps.append(ReductionStep(cursor, r, "beta"))
            cursor = r
            continue
        break
    return steps


def show_reduction(core: BootstrapCore, steps: list[ReductionStep]) -> str:
    lines = [f"{pretty(core, s.before)} => {pretty(core, s.after)}  [{s.kind}]"
             for s in steps]
    if not lines:
        return "(already in normal form)"
    return "\n".join(lines)
```

- [ ] **Step 4: 运行测试**

Run: `pytest py_nanobruijn/test_teaching.py::TestReduce -q`
Expected: PASS。若 `test_delta_reduction_steps` 失败（steps 为空，说明 `unfold_def` 返回 None），检查 Task 2 的 `_const_or_bound` 是否已为 `id` 填充 universe 参数（`u0`）；`unfold_def` 要求常量应用的 level 参数数量等于声明 uparams 数量（tc_whnf.py:100）。

- [ ] **Step 5: 运行全量测试 + 提交**

Run: `pytest py_nanobruijn/test_teaching.py -q && pytest py_nanobruijn -q`
Expected: PASS

```bash
git add py_nanobruijn/teaching/reduce.py py_nanobruijn/test_teaching.py
git commit -m "feat(teaching): step-by-step beta/delta reduction"
```

---

### Task 5: REPL teaching/repl.py

**Files:**
- Create: `py_nanobruijn/teaching/repl.py`
- Test: `py_nanobruijn/test_teaching.py`（追加 TestRepl 类）

**Interfaces:**
- Consumes: `BootstrapCore`、`parse_expr`、`pretty`、`reduce_steps`/`show_reduction`、`CheckTimeoutError`
- Produces: `Repl` 类（`__init__(core, timeout_secs=5.0)`、`process_line(line) -> str`、`run(stdin=None, stdout=None) -> int`）；命令：`#help`/`#quit`/`#env`/`#print <name>`/`#reduce <e>`/默认 `#check <e>`；`process_line("#quit")` 抛 `EOFError`（run 捕获并返回 0）

- [ ] **Step 1: 写失败测试**（追加 import：`from .teaching.repl import Repl`、`import io` 放在类内使用处）

```python
class TestRepl:
    def make_repl(self):
        return Repl(make_bootstrap())

    def test_check_expr(self):
        r = self.make_repl()
        out = r.process_line("fun (x : Prop) => x")
        assert "fun (x : Prop) => x :" in out
        assert "Prop -> Prop" in out

    def test_check_at_app(self):
        r = self.make_repl()
        out = r.process_line("#check @And True True")
        assert ": Prop" in out

    def test_reduce(self):
        r = self.make_repl()
        out = r.process_line("#reduce (fun (x : Prop) => x) True.intro")
        assert "[beta]" in out
        assert "True.intro" in out

    def test_print(self):
        r = self.make_repl()
        out = r.process_line("#print And.intro")
        assert "And.intro :" in out
        assert "And" in out

    def test_print_definition_value(self):
        r = self.make_repl()
        out = r.process_line("#print id")
        assert "id :" in out
        assert "fun" in out

    def test_env(self):
        r = self.make_repl()
        out = r.process_line("#env")
        assert "And" in out
        assert "True" in out

    def test_unknown_command(self):
        r = self.make_repl()
        assert "unknown command" in r.process_line("#bogus").lower()

    def test_error_friendly(self):
        r = self.make_repl()
        out = r.process_line("#check x")
        assert "error" in out.lower()
        assert "Traceback" not in out

    def test_quit(self):
        r = self.make_repl()
        with pytest.raises(EOFError):
            r.process_line("#quit")

    def test_run_loop(self):
        import io
        r = self.make_repl()
        buf = io.StringIO()
        code = r.run(stdin=io.StringIO("#env\n#quit\n"), stdout=buf)
        assert code == 0
        assert "And" in buf.getvalue()
```

- [ ] **Step 2: 运行确认失败**

Run: `pytest py_nanobruijn/test_teaching.py::TestRepl -q`
Expected: FAIL（ModuleNotFoundError: teaching.repl）

- [ ] **Step 3: 实现 repl.py**

```python
# py_nanobruijn/teaching/repl.py
from __future__ import annotations

import sys

from ..errors import CheckTimeoutError
from ..ptr import ExprPtr
from .core import BootstrapCore
from .parser import parse_expr
from .pretty import pretty
from .reduce import reduce_steps, show_reduction

BANNER = (
    "py-nanobruijn teaching REPL\n"
    "输入表达式查看类型（等价 #check），或使用命令：#check/#reduce/#print/#env/#help/#quit\n"
    "语法：fun (x : A) => e、∀ (x : A), e、A -> B、@Const、Type、Prop"
)


class Repl:
    def __init__(self, core: BootstrapCore, timeout_secs: float = 5.0):
        self.core = core
        self.timeout_secs = float(timeout_secs)

    # ---------- 命令 ----------

    def process_line(self, line: str) -> str:
        text = line.strip()
        if not text:
            return ""
        if text.startswith("#"):
            return self._command(text)
        return self._check(text)

    def _command(self, text: str) -> str:
        parts = text[1:].split(maxsplit=1)
        cmd = parts[0]
        rest = parts[1] if len(parts) > 1 else ""
        if cmd == "help":
            return BANNER
        if cmd == "quit":
            raise EOFError()
        if cmd == "env":
            return "\n".join(self.core.constants())
        if cmd == "print":
            return self._print_const(rest)
        if cmd == "reduce":
            return self._run_reduce(rest)
        if cmd == "check":
            return self._check(rest)
        return f"unknown command #{cmd} (try #help)"

    def _check(self, text: str) -> str:
        try:
            e = parse_expr(self.core, text)
            tc = self.core.make_type_checker(self.timeout_secs)
            ty = tc.infer(e, 'check')
            return f"{pretty(self.core, e)} : {pretty(self.core, ty)}"
        except (ValueError, CheckTimeoutError) as err:
            return f"error: {err}"
        except Exception as err:  # noqa: BLE001 - REPL 顶层兜底
            return f"error: {type(err).__name__}: {err}"

    def _run_reduce(self, text: str) -> str:
        try:
            e = parse_expr(self.core, text)
            tc = self.core.make_type_checker(self.timeout_secs)
            return show_reduction(self.core, reduce_steps(tc, e))
        except (ValueError, CheckTimeoutError) as err:
            return f"error: {err}"
        except Exception as err:  # noqa: BLE001
            return f"error: {type(err).__name__}: {err}"

    def _print_const(self, text: str) -> str:
        text = text.strip()
        if not text:
            return "usage: #print <name>"
        ptr = self.core.name_to_ptr(text)
        decl = self.core.env.declars.get(ptr)
        if decl is None:
            return f"error: unknown constant {text!r}"
        from ..env import Axiom, Definition, OpaqueDecl, Theorem
        lines = [f"{self.core.name_to_string(decl.info.name)} : "
                 f"{pretty(self.core, ExprPtr.closed(decl.info.ty))}"]
        if isinstance(decl, (Definition, Theorem, OpaqueDecl)):
            lines.append(f"  = {pretty(self.core, ExprPtr.closed(decl.value))}")
        elif isinstance(decl, Axiom):
            lines.append("  (axiom)")
        return "\n".join(lines)

    # ---------- 主循环 ----------

    def run(self, stdin=None, stdout=None) -> int:
        stdin = stdin or sys.stdin
        stdout = stdout or sys.stdout
        print(BANNER, file=stdout)
        print(f"已加载 {len(self.core.constants())} 个常量，输入 #help 查看帮助", file=stdout)
        while True:
            try:
                line = input("> ") if stdin is sys.stdin else stdin.readline()
            except EOFError:
                return 0
            if not line:
                if stdin is not sys.stdin:
                    return 0
                continue
            try:
                out = self.process_line(line)
            except EOFError:
                return 0
            if out:
                print(out, file=stdout)
```

要点：
- `#quit` 抛内置 `EOFError`（`process_line` 测试可断言；`run` 捕获返回 0）
- 每行新 `TypeChecker`（干净缓存 + `timeout_secs` 防卡死，老项目痛点由 `CheckTimeoutError` 兜底）
- 错误一行输出，无 traceback

- [ ] **Step 4: 运行测试**

Run: `pytest py_nanobruijn/test_teaching.py::TestRepl -q`
Expected: PASS

- [ ] **Step 5: 全量回归 + 提交**

Run: `pytest py_nanobruijn -q`
Expected: PASS（189 + 新增全过）

```bash
git add py_nanobruijn/teaching/repl.py py_nanobruijn/test_teaching.py
git commit -m "feat(teaching): interactive REPL with check/reduce/print/env commands"
```

---

### Task 6: CLI 集成 + 文档 + 全量回归

**Files:**
- Modify: `py_nanobruijn/__main__.py`（加 repl 子命令）
- Modify: `README.md`（文档提及 repl 命令）
- Test: `py_nanobruijn/test_teaching.py`（追加 TestCli 类）

**Interfaces:**
- Consumes: `Repl`（Task 5）、现有 `main(argv)` 结构
- Produces: `py-nanobruijn repl [--timeout SECS]` 子命令；`python -m py_nanobruijn repl` 可运行

- [ ] **Step 1: 写失败测试**（追加到 test_teaching.py）

```python
class TestCli:
    def test_cli_repl_subprocess(self):
        import subprocess
        import sys
        proc = subprocess.run(
            [sys.executable, "-m", "py_nanobruijn", "repl"],
            input="#env\n#quit\n", capture_output=True, text=True, timeout=30,
        )
        assert proc.returncode == 0
        assert "And" in proc.stdout
```

- [ ] **Step 2: 运行确认失败**

Run: `pytest py_nanobruijn/test_teaching.py::TestCli -q`
Expected: FAIL（exit code 2：unrecognized arguments: repl）

- [ ] **Step 3: 实现 __main__.py 修改**

现有 `main()` 结构（`__main__.py:74-91`）：

```python
def _run_repl(args: argparse.Namespace) -> int:
    from .teaching.core import make_bootstrap
    from .teaching.repl import Repl
    core = make_bootstrap()
    return Repl(core, timeout_secs=args.timeout or 5.0).run()
```

`main()` 中三处修改：
1. 命令集合（第 77 行）加 `"repl"`：`if argv and argv[0] not in {"check", "inspect", "repl", "-h", "--help"}:`
2. `subparsers.add_parser("repl", help="interactive teaching REPL")` + `repl_cmd.add_argument("--timeout", type=float, default=5.0, help="seconds before aborting a declaration check (default 5.0)")`
3. 分发末尾：`if args.command == "check": return _run_check(args)` / `if args.command == "inspect": return _run_inspect(args)` / `return _run_repl(args)`

- [ ] **Step 4: 运行测试**

Run: `pytest py_nanobruijn/test_teaching.py::TestCli -q`
Expected: PASS

- [ ] **Step 5: README 文档更新**

README.md 末尾追加一节：

```markdown
## Teaching REPL (Python)

```
python -m py_nanobruijn repl
```

交互式教学 REPL：内置 Prop 逻辑核心（True/False/And/Or/Iff/Eq/Not/propext/id/
Function.comp/flip），输入表达式查看类型（#check）、逐步 β/δ 归约（#reduce）、
打印常量定义（#print）。命令：#check/#reduce/#print/#env/#help/#quit。
```

- [ ] **Step 6: 全量回归 + lint**

Run: `pytest py_nanobruijn -q`
Expected: PASS
Run: `ruff check py_nanobruijn`
Expected: 0 errors（若有风格问题按提示修复）

- [ ] **Step 7: 提交**

```bash
git add py_nanobruijn/__main__.py py_nanobruijn/test_teaching.py README.md
git commit -m "feat(cli): add repl subcommand + README docs"
```