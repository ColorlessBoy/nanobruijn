# py_nanobruijn 第 7 步（工程收尾）实施计划

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** 完成 py_nanobruijn 第二次重构的最后一步：ruff lint 基线清零、真实超时控制、pytest/ruff CI，使工程达到可提交、可 CI 验证的状态。

**Architecture:** 全部改动集中在 `py_nanobruijn/` 包、`pyproject.toml`、`.github/workflows/ci.yaml`。超时控制采用**检查点式**：在 whnf/defeq/level 循环内周期性检查 `time.monotonic()` 与 deadline，超时抛 `CheckTimeoutError`；deadline 挂在 `TcCtx` 上（TypeChecker 构造时设置），因此 `LevelOpsMixin`（self 为 TcCtx）与 `DefEqMixin`/`TypeChecker` 的循环都能访问。

**Tech Stack:** Python 3.10+、pytest、ruff（当前 0.16.3）。

**Spec:** 无独立 spec 文档；需求来自最新 commit 38da3b1 的 commit message："补齐 pytest/ruff CI、治理现有 lint 基线（218 个问题）、实现真实超时控制"（REPL/trace 交互经用户确认**不在本次范围**，后续单独 brainstorm）。

## Global Constraints

- 验证命令（统一在项目根执行，venv 见 Task 1）：
  - 测试：`.venv/bin/python -m pytest -q` → 基线 **183 passed**；最终 **189 passed**（Task 2 加 1 个 mixin 测试，Task 4 加 5 个超时测试）
  - lint：`.venv/bin/ruff check py_nanobruijn` → 必须 **0 errors**（最终态；中间态在任务内自洽）
- 纯 lint 修复任务（Task 1/2/3）**禁止改变任何运行行为**：只动 import、注解写法、变量命名、if 合并；不重构逻辑。
- 每个任务末尾独立 commit，commit message 附验证证据（如 "ruff 0 errors, pytest 183 passed"）。
- 提交前必须跑完该任务的完整验证命令（verification-before-completion：fresh 证据，不依赖记忆）。
- 当前分支 `fix/clippy-warnings` 继续工作，不另开分支。
- 超时默认禁用：`timeout_secs <= 0` 时行为与现在完全一致。

---

### Task 1: 环境准备 + ruff 自动修复基线

**Files:**
- Create: `.venv/`（git-ignored）
- Modify: `.gitignore`（加 `.venv/`）
- Modify: `pyproject.toml`（[tool.ruff] 补 `select`，锁定规则基线）
- 全包文件（ruff --fix 自动修改）

**Interfaces:**
- Consumes: 无
- Produces: 可复现的验证环境；pyproject 中锁定 ruff 版本，CI 与本地规则一致

- [ ] **Step 1: 创建 venv 并安装开发依赖**

```bash
python3 -m venv .venv
.venv/bin/pip install -e '.[dev]'
```

Expected: `.venv/bin/ruff --version` 可用；`.venv/bin/python -m pytest -q` → 183 passed（基线确认）。

- [ ] **Step 2: 在 .gitignore 追加 venv 忽略**

在 `.gitignore` 的 `py_nanobruijn/__pycache__/` 行附近追加：

```
.venv/
```

- [ ] **Step 3: 锁定 ruff 版本到 dev 依赖**

验证发现：`ruff check py_nanobruijn --isolated` 也报 218 errors——说明 ruff 0.16.3 的**默认规则集**已包含 UP/RUF/SIM/BLE/PLR 等规则，与本地配置无关。因此**不要**显式写 `select`（显式 select 反而会改变规则集合，例如 `select = ["E","F","I","UP","B","SIM","RUF","PL","BLE"]` 报 435 errors ≠ 218）。正确做法是**锁定 ruff 版本**，让 CI 与本地用同一版本、同一默认规则集。

`pyproject.toml` 的 `[project.optional-dependencies].dev` 改为：

```toml
dev = ["pytest>=8", "ruff==0.16.3"]
```

然后**重新安装**以应用锁定版本：

```bash
.venv/bin/pip install -e '.[dev]'
.venv/bin/ruff --version
```

Expected: `.venv/bin/ruff --version` → 0.16.3；`.venv/bin/ruff check py_nanobruijn --statistics` → 约 218 errors（与之前一致，共 15 种规则代码：UP006×57、UP045×49、F811×31、I001×28、UP035×17、RUF100×11、RUF059×7、RUF023×7、SIM102×2、RUF015×2、PLR1716×2、F401×2、UP007×1、RUF022×1、BLE001×1）。

- [ ] **Step 4: 运行 ruff 自动修复**

```bash
.venv/bin/ruff check py_nanobruijn --fix
```

Expected: 剩余约 59 个不可自动修复的问题（F811 31 + RUF059 7 + SIM102 2 + RUF015 2 + BLE001 1 + F401 剩余 2 + 其他），159 个可修项已被修复。

- [ ] **Step 5: 运行测试验证自动修复未破坏行为**

```bash
.venv/bin/python -m pytest -q
```

Expected: **183 passed**（0.9s 左右）。若失败，逐项审查 --fix 的改动（重点：被删除的 noqa 注释是否删掉了有副作用的 import），回退有问题的文件后手动处理。

- [ ] **Step 6: 审查 diff 只包含风格改动**

```bash
git diff --stat
git diff py_nanobruijn | less   # 抽查 UP006/UP045/I001 等改动
```

Expected: 改动仅为注解写法（`typing.Optional[X]` → `X | None`、`List` → `list`）、import 排序、noqa 清理；无逻辑分支变化。

- [ ] **Step 7: Commit**

```bash
git add -A
git commit -m "chore(ruff): apply auto-fix baseline, pin rule set in pyproject (pytest 183 passed)"
```

---

### Task 2: 清理 F811 mixin 桩声明（tc_whnf.py）

**Files:**
- Modify: `py_nanobruijn/tc_whnf.py:40-106`

**Interfaces:**
- Consumes: Task 1 已把 159 个自动问题清掉
- Produces: F811 归零；`TypeChecker` 公开 API（is_def_eq/assert_def_eq/def_eq 等 30+ 方法）保持可用

背景：第 6 步把 monkey patch 改为 `TypeChecker(InferenceMixin, DefEqMixin)` 后，`tc_whnf.py:40-73` 残留了为 pyright 服务的空桩声明（`def is_def_eq(self, e1, e2) -> bool: ...`），`76-106` 又用 `is_def_eq = DefEqMixin.is_def_eq` 显式赋值覆盖，二者重复触发 F811。

**方案：删除 40-73 行的桩声明块（含第 40 行遗留注释 `# --- Patched by tc_defeq.py ---`），保留 76-106 行的显式赋值块**。理由：桩声明与显式赋值重复；赋值块既提供运行时实现也提供 pyright 类型锚点，是最小改动。

- [ ] **Step 1: 写回归测试确认 TypeChecker 方法可用**

在 `py_nanobruijn/test_tc_whnf.py` 末尾追加：

```python
# ============================================================
# Mixin API surface (regression for F811 cleanup)
# ============================================================


def test_type_checker_mixin_api_surface():
    ctx = make_ctx()
    env = make_env()
    tc = TypeChecker(ctx, env)
    for name in ("is_def_eq", "assert_def_eq", "def_eq", "def_eq_inner",
                 "def_eq_quick_check", "def_eq_sort", "def_eq_const",
                 "def_eq_local", "def_eq_proj", "def_eq_binder_aux",
                 "def_eq_app", "def_eq_nat", "cheap_eq", "uf_find",
                 "uf_union", "defeq_normalize_pair", "delta",
                 "try_eta_expansion", "is_proof", "proof_irrel_eq"):
        assert callable(getattr(tc, name)), f"{name} missing or not callable"
```

Expected: PASS（当前代码已通过，作为清理后的守卫）。

- [ ] **Step 2: 删除桩声明块**

删除 `py_nanobruijn/tc_whnf.py` 第 40 行的 `# --- Patched by tc_defeq.py ---` 注释，以及 41-73 行的全部空桩声明（`def is_def_eq(self, e1, e2) -> bool: ...` 等）。保留 74 行起的注释与 76-106 行显式赋值。

Expected: `ruff check py_nanobruijn --statistics` 中 F811 计数归零；`.venv/bin/python -m pytest -q` → 184 passed（含 Step 1 新测试）。

- [ ] **Step 3: 验证 WHNF/defeq 行为未变**

```bash
.venv/bin/python -m pytest py_nanobruijn/test_tc_whnf.py py_nanobruijn/test_tc_defeq.py -q
```

Expected: 全部通过（覆盖 unfold/defeq 主路径）。

- [ ] **Step 4: Commit**

```bash
git add py_nanobruijn/tc_whnf.py py_nanobruijn/test_tc_whnf.py
git commit -m "refactor(tc_whnf): drop redundant mixin stub declarations, kill F811 (ruff clean, pytest 184 passed)"
```

---

### Task 3: 剩余手动 lint 修复（RUF059 / SIM102 / BLE001 / F401 / RUF015 / PLR1716）

**Files:**
- Modify: `py_nanobruijn/__main__.py:37`（BLE001）
- Modify: `py_nanobruijn/dag.py:3,8`（F401）
- Modify: `py_nanobruijn/tc_context.py:373`（SIM102）
- Modify: `py_nanobruijn/tc_defeq.py:392`（SIM102）
- Modify: `py_nanobruijn/test_parser.py:34,46`（RUF015）
- Modify: `py_nanobruijn/test_full_suite.py:300,462`（PLR1716）
- Modify: `py_nanobruijn/test_tc_context.py:227,253,276`（RUF059）
- Modify: `py_nanobruijn/test_tc_infer.py:116`（RUF059）

**Interfaces:**
- Consumes: Task 2 完成后 F811 已清零
- Produces: ruff 0 errors 的中间态

- [ ] **Step 1: 修复 __main__.py BLE001（CLI 顶层防御性捕获，加 noqa 说明）**

`py_nanobruijn/__main__.py:37`：

```python
    except Exception as error:  # noqa: BLE001 - CLI top-level catch: surface any failure as exit 1
```

- [ ] **Step 2: 修复 dag.py F401（删除未使用 import）**

`py_nanobruijn/dag.py:3`：`from typing import Optional, TYPE_CHECKING, List` → 删除 `List`
`py_nanobruijn/dag.py:8`：`from .ptr import ExprPtr, CorePtr, LevelPtr, LevelsPtr, NamePtr` → 删除 `LevelsPtr`

- [ ] **Step 3: 修复 tc_context.py SIM102（合并嵌套 if）**

`py_nanobruijn/tc_context.py:372-374`：

```python
    if sh_amt == 0 and sh_cut == 0:
        if nlbv <= offset:
            return ExprPtr.from_nlbv(e, nlbv)
```

→

```python
    if sh_amt == 0 and sh_cut == 0 and nlbv <= offset:
        return ExprPtr.from_nlbv(e, nlbv)
```

- [ ] **Step 4: 修复 tc_defeq.py SIM102（合并嵌套 if）**

`py_nanobruijn/tc_defeq.py:391-393`：

```python
        if l_expr.tag == 'Const' and r_expr.tag == 'Const':
            if len(l_args) == len(r_args) and not self.defeq_neg_lookup(x, y):
```

→

```python
        if (l_expr.tag == 'Const' and r_expr.tag == 'Const'
                and len(l_args) == len(r_args) and not self.defeq_neg_lookup(x, y)):
```

注意：`defeq_neg_lookup` 只在 `l_args/r_args` 长度相等时调用，合并后短路求值顺序不变，行为等价。

- [ ] **Step 5: 修复 test_parser.py RUF015**

两处 `name = list(ef.declars.keys())[0]`（第 34、46 行）→

```python
    name = next(iter(ef.declars.keys()))
```

- [ ] **Step 6: 修复 test_full_suite.py PLR1716**

第 300、462 行两处 `if 0 < y and y <= x:` → `if 0 < y <= x:`

- [ ] **Step 7: 修复 test_tc_context.py RUF059（未使用的解包变量）**

- 第 227 行 `head, name, lvls, args = result`：`head`/`lvls` 未用 → `_, name, _, args`
- 第 253 行 `name, style, binder_ty, body_expr = result`：`name`/`binder_ty`/`body_expr` 未用 → `_, style, _, _`
- 第 276 行 `name, style, binder_ty = result`：`binder_ty` 未用 → `name, style, _`

- [ ] **Step 8: 修复 test_tc_infer.py RUF059**

第 116 行 `_, _, pi_bt, pi_body = unfolded`：`pi_body` 未用 → `_, _, pi_bt, _`

- [ ] **Step 9: 全量验证**

```bash
.venv/bin/ruff check py_nanobruijn
.venv/bin/python -m pytest -q
```

Expected: ruff **0 errors**；pytest **184 passed**。

- [ ] **Step 10: Commit**

```bash
git add -A
git commit -m "chore(lint): fix remaining manual ruff issues (BLE001, SIM102, F401, RUF015, PLR1716, RUF059) — ruff 0 errors, pytest 184 passed"
```

---

### Task 4: 检查点式超时控制（TDD）

**Files:**
- Modify: `py_nanobruijn/errors.py`（新增 `CheckTimeoutError`）
- Modify: `py_nanobruijn/dag.py`（`TcCtx` 增加 `timeout_deadline` 与 `check_timeout`）
- Modify: `py_nanobruijn/tc_whnf.py`（`TypeChecker.__init__` 接收 `timeout_secs`；whnf 循环插入检查点）
- Modify: `py_nanobruijn/tc_defeq.py`（`def_eq_binder_aux` 循环插入检查点）
- Modify: `py_nanobruijn/level_ops.py`（`level_succs` 循环插入检查点；`simplify` 无循环不设）
- Modify: `py_nanobruijn/config.py`（`declaration_timeout_secs` 改为 `float`）
- Modify: `py_nanobruijn/services/checker.py`（把 config 超时传给 TypeChecker）
- Modify: `py_nanobruijn/__main__.py`（check 子命令加 `--timeout`）
- Create: `py_nanobruijn/test_timeout.py`

**Interfaces:**
- Consumes: `Config.declaration_timeout_secs`（现为 int=0，改为 float=0.0）；`TypeChecker.__init__` 现有签名 `(ctx, env, declar_info=None)` 追加位置参数（保持向后兼容，`declar_info` 仍是第三位置参数）
- Produces: `TcCtx.timeout_deadline: float`（0 = 禁用）、`TcCtx.check_timeout()`、`TypeChecker(timeout_secs: float = 0.0)`（第 4 个位置参数）、`CheckTimeoutError`、CLI `--timeout` 秒（float）

实现要点：
1. deadline 放 `TcCtx`，因为 `LevelOpsMixin` 方法的 self 是 `TcCtx`；`TypeChecker` 的循环通过 `self.ctx.check_timeout()` 访问。
2. 检查点用**迭代计数器节流**：每 256 次迭代检查一次 `time.monotonic()`，避免热路径开销（`cedar` 729MB 用例仍需可跑）。
3. 超时抛 `CheckTimeoutError(PyNanobruijnError)`，`CheckerService.check_all` 现有的 `except Exception` 会将其记为 diagnostic（keep_going）或上抛。

- [ ] **Step 1: 写失败测试 `py_nanobruijn/test_timeout.py`**

```python
from __future__ import annotations

import time

import pytest

from .dag import LeanDag, TcCtx
from .env import Abbrev, DeclarInfo, Definition, Env, EnvLimit
from .errors import CheckTimeoutError
from .expr import Expr
from .name import Name
from .tc_whnf import TypeChecker


def make_ctx() -> TcCtx:
    dag = LeanDag.with_capacity(None, 0)
    return TcCtx(dag)


def insert_name(ctx: TcCtx, s: str, pfx: int = 0) -> int:
    return ctx.dag.insert_name(Name.str(pfx, ctx.dag.insert_string(s)))


def make_env() -> Env:
    return Env(declars={}, limit=EnvLimit("pp_unlimited"))


def make_tc(timeout_secs: float = 0.0) -> TypeChecker:
    return TypeChecker(make_ctx(), make_env(), timeout_secs=timeout_secs)


def add_loop_declaration(ctx: TcCtx, env: Env, name: str) -> None:
    """loop : Sort 0, loop := loop  (self-referential constant: infinite unfold)."""
    n = insert_name(ctx, name)
    loop_core = ctx.dag.insert_expr(Expr.const(n, ctx.dag.insert_uparams(())))[0]
    env.declars[n] = Definition(
        info=DeclarInfo(name=n, uparams=ctx.dag.insert_uparams(()), ty=ctx.mk_sort(0).core),
        value=loop_core,
        hint=Abbrev(),
        safety="safe",
    )


def test_timeout_disabled_by_default():
    tc = make_tc(timeout_secs=0.0)
    assert tc.ctx.timeout_deadline == 0.0
    tc.ctx.check_timeout()  # must not raise


def test_checkpoint_triggers_after_deadline():
    tc = make_tc(timeout_secs=1.0)
    tc.ctx.timeout_deadline = time.monotonic() - 1.0  # force expiry
    with pytest.raises(CheckTimeoutError):
        tc.ctx.check_timeout()


def test_whnf_hits_checkpoint_on_infinite_unfold():
    ctx = make_ctx()
    env = make_env()
    add_loop_declaration(ctx, env, "loop")
    tc = TypeChecker(ctx, env, timeout_secs=0.5)
    const_expr = ctx.mk_const(insert_name(ctx, "loop"), ctx.dag.insert_uparams(()))
    started = time.monotonic()
    with pytest.raises(CheckTimeoutError):
        tc.whnf(const_expr)
    elapsed = time.monotonic() - started
    assert elapsed >= 0.3, f"timeout fired too early: {elapsed:.3f}s"


def test_defeq_hits_checkpoint_on_infinite_loop():
    ctx = make_ctx()
    env = make_env()
    add_loop_declaration(ctx, env, "loop2")
    tc = TypeChecker(ctx, env, timeout_secs=0.5)
    const_expr = ctx.mk_const(insert_name(ctx, "loop2"), ctx.dag.insert_uparams(()))
    with pytest.raises(CheckTimeoutError):
        tc.assert_def_eq(const_expr, ctx.mk_sort(0))


def test_cli_flag_sets_config_timeout():
    from .config import Config
    config = Config(export_file_path="x", declaration_timeout_secs=1.5)
    assert config.declaration_timeout_secs == 1.5
```

Expected: 前两个测试失败（`TypeChecker` 不接受 `timeout_secs`、`TcCtx` 无 `timeout_deadline`）；`test_whnf_*`/`test_defeq_*` 在实现前**无限循环挂起**（无检查点）——所以写完后只跑 `pytest py_nanobruijn/test_timeout.py::test_timeout_disabled_by_default -x` 确认失败形态即可，不要全跑；`test_cli_flag_sets_config_timeout` 是 float 类型回归守卫（dataclass 不校验类型，实现前也通过，其价值是防止未来把 `--timeout` 截断为 int）。

**注意**：未实现检查点前，不要执行 `test_whnf_hits_checkpoint_on_infinite_unfold` 或 `test_defeq_hits_checkpoint_on_infinite_loop`（会真挂起；如误跑用 Ctrl-C 终止）。

- [ ] **Step 2: 实现错误类型与 TcCtx 检查点**

`py_nanobruijn/errors.py` 追加：

```python
class CheckTimeoutError(PyNanobruijnError):
    """A declaration check exceeded its configured time budget."""
```

`py_nanobruijn/dag.py` 的 `TcCtx` 类：`__slots__`（第 217 行）追加 `'timeout_deadline'`，`__init__` 追加初始化：

```python
    __slots__ = ('dag', 'export_file', 'local_depth', '_name_cache', 'timeout_deadline')
```

```python
        self.timeout_deadline: float = 0.0  # 0.0 = disabled
```

`TcCtx` 类内新增方法：

```python
    def check_timeout(self) -> None:
        if self.timeout_deadline > 0 and time.monotonic() > self.timeout_deadline:
            raise CheckTimeoutError(
                f"declaration check exceeded its timeout budget"
            )
```

`dag.py` 顶部 import 追加：`import time` 和 `from .errors import CheckTimeoutError`。

**注意**：`TcCtx` 用了 `__slots__`，忘加字段名会导致 `AttributeError: 'TcCtx' object has no attribute 'timeout_deadline'`——必须先改 `__slots__`。

- [ ] **Step 3: TypeChecker 接收 timeout_secs 并设置 deadline**

`py_nanobruijn/tc_whnf.py` 的 `__init__`：

```python
    def __init__(self, ctx: TcCtx, env: Env, declar_info=None, timeout_secs: float = 0.0):
        self.ctx = ctx
        self.env = env
        self.cache = TcCache()
        self.declar_info = declar_info
        self.local_types = []
        self.timeout_secs = float(timeout_secs or 0.0)
        if self.timeout_secs > 0:
            self.ctx.timeout_deadline = time.monotonic() + self.timeout_secs
        self._timeout_iter = 0
```

`tc_whnf.py` 顶部 import 追加：`import time`。

- [ ] **Step 4: whnf 循环插入检查点**

`whnf_inner` 的 `while True:`（约第 166 行）循环体顶部追加：

```python
        self._timeout_iter += 1
        if self._timeout_iter & 0xFF == 0:
            self.ctx.check_timeout()
```

`whnf_no_unfolding_aux` 的 `while True:`（约第 207 行）循环体顶部同样追加上述两行。

- [ ] **Step 5: defeq 检查点插入 `def_eq_inner` 递归入口**

`py_nanobruijn/tc_defeq.py` 的 `def_eq_inner`（约第 29 行）函数体开头追加：

```python
    self._timeout_iter += 1
    if self._timeout_iter & 0xFF == 0:
        self.ctx.check_timeout()
```

**不要**只放在 `def_eq_binder_aux` 的循环里：def_eq 对自引用常量（如 `Const loop`）会经 `lazy_delta_step` 无限**递归** `def_eq_inner`，永远不会进入 binder 循环——检查点必须覆盖递归入口。

- [ ] **Step 6: level 循环插入检查点**

`py_nanobruijn/level_ops.py` 的 `level_succs` 中 `while True:`（第 9 行）循环内追加：

```python
        self.check_timeout()
```

（self 即 TcCtx；`simplify` 是递归实现、无循环，其递归深度受表达式结构限制，不设检查点，保持默认禁用时零开销路径不变。）

- [ ] **Step 7: 运行测试**

```bash
.venv/bin/python -m pytest py_nanobruijn/test_timeout.py -v
.venv/bin/python -m pytest -q
```

Expected: 5 个新测试全过；全量 **189 passed**（183 原有 + 5 超时测试 + Task 2 的 1 个 mixin 测试）。

- [ ] **Step 8: CheckerService 传递 config 超时**

`py_nanobruijn/services/checker.py` 的 `make_type_checker`：

```python
    def make_type_checker(self, declaration: Declar) -> TypeChecker:
        from ..dag import TcCtx

        ctx = TcCtx(self.export.dag)
        ctx.export_file = self.export
        env = Env(self.export.declars, limit=EnvLimit("by_name", declaration.info.name))
        return TypeChecker(
            ctx, env,
            declar_info=declaration.info,
            timeout_secs=float(self.export.config.declaration_timeout_secs),
        )
```

- [ ] **Step 9: config 改为 float + CLI 加 --timeout**

`py_nanobruijn/config.py:26`：

```python
    declaration_timeout_secs: float = 0.0
```

`py_nanobruijn/__main__.py` 的 `_add_check_options` 追加：

```python
    command.add_argument("--timeout", type=float, default=0.0,
                         help="abort a declaration check after this many seconds (0 = no timeout)")
```

`_run_check` 中设置：

```python
    config.declaration_timeout_secs = args.timeout
```

- [ ] **Step 10: CLI 冒烟验证**

```bash
.venv/bin/python -m py_nanobruijn check test_resources/Empty/export --timeout 30
```

Expected: `checked=... failed=0 skipped=... elapsed_ms=...` 且退出码 0。再验证超时路径：

```bash
.venv/bin/python -m py_nanobruijn check test_resources/Empty/export --timeout 0.0000001 --json
```

Expected: 因空 export 无声明，不触发超时（无声明可检查）；以退出码 0 结束，说明 `--timeout` 参数被接受。真实超时路径已由 test_timeout.py 覆盖。

- [ ] **Step 11: 全量验证 + Commit**

```bash
.venv/bin/ruff check py_nanobruijn
.venv/bin/python -m pytest -q
```

Expected: ruff **0 errors**；pytest **189 passed**。

```bash
git add -A
git commit -m "feat(timeout): checkpoint-style declaration timeout via TcCtx deadline (pytest 189 passed, ruff clean)"
```

---

### Task 5: pytest/ruff CI

**Files:**
- Modify: `.github/workflows/ci.yaml`

**Interfaces:**
- Consumes: Task 1 的 pyproject ruff 规则声明、Task 3/4 后 ruff 0 errors + pytest 189 passed
- Produces: push/PR 时自动跑 Python 检查

- [ ] **Step 1: 在 ci.yaml 增加 Python job**

在现有 `build-and-test` job 后追加（保持 Rust job 不动）：

```yaml
  python-check:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4

      - name: Set up Python
        uses: actions/setup-python@v5
        with:
          python-version: "3.12"

      - name: Install package and dev deps
        run: python -m pip install -e '.[dev]'

      - name: Lint
        run: ruff check py_nanobruijn

      - name: Test
        run: python -m pytest -q
```

- [ ] **Step 2: 本地验证 yaml 语法与命令可执行**

```bash
python3 -c "import yaml, pathlib; yaml.safe_load(pathlib.Path('.github/workflows/ci.yaml').read_text()); print('yaml ok')"
.venv/bin/ruff check py_nanobruijn
.venv/bin/python -m pytest -q
```

Expected: `yaml ok`；ruff 0 errors；pytest 189 passed（CI 中命令与本地一致）。

- [ ] **Step 3: Commit**

```bash
git add .github/workflows/ci.yaml
git commit -m "ci: add python lint + test job to GitHub Actions (pytest 189 passed, ruff clean)"
```

---

### Task 6: 收尾验证

**Files:**
- Modify: `py_nanobruijn/README.md`（lint/测试状态与超时用法）

**Interfaces:**
- Consumes: 全部前序任务
- Produces: 文档与事实一致

- [ ] **Step 1: 更新 README 状态**

`py_nanobruijn/README.md` 中 "Rlint 状态" 一节改为：

```markdown
## 状态

- `ruff check py_nanobruijn`: 0 warnings
- `pytest`: 189/189 passed
```

并在 CLI 用法中补一行：

```bash
# 单声明超时控制（秒，默认 0 = 不禁用）
python3 -m py_nanobruijn check path/to/export.ndjson --timeout 30
```

- [ ] **Step 2: 全量最终验证**

```bash
.venv/bin/ruff check py_nanobruijn
.venv/bin/python -m pytest -q
git status --short
```

Expected: ruff 0 errors；pytest 189 passed；工作树仅剩 README 改动。

- [ ] **Step 3: Commit**

```bash
git add py_nanobruijn/README.md
git commit -m "docs(readme): update status (189 tests, ruff clean) and document --timeout"
```

- [ ] **Step 4: 汇报**

向用户汇报：提交列表（`git log --oneline -6`）、最终验证输出、遗留项（REPL/trace 待后续 brainstorm、`cedar` 大文件可用 `--timeout` 治理）。
