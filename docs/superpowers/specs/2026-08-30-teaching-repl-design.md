# 教学 REPL 设计（teaching REPL）

日期：2026-08-30
状态：已批准（用户确认整体设计；infer 推导树列为 v1 增强，默认不做）

## 背景

参考老项目 [lean4_lambda_calculator](https://github.com/ColorlessBoy/lean4_lambda_calculator)
的 `query_const.lean`（手工定义逻辑常量 + `#print`/`#check` 查询）的思路，在
py_nanobruijn 上实现一个交互式教学 REPL。老项目的问题是 bug + 性能差，复杂表达式
推断不出类型就卡死；本设计复用 py_nanobruijn 的真实内核（infer/whnf/def_eq），
由现有 timeout 机制兜底，不复制老项目的性能问题。

## 目标

- 交互式 REPL：学生输入表达式或查询常量，得到类型/定义/归约步骤
- 内置逻辑核心：仿老项目手工定义 Prop 逻辑（And/Or/Iff/Eq/Not/True/False 等），
  启动即用，不依赖 NDJSON export 文件
- 复用真实内核：类型检查/归约走 py_nanobruijn 的 `TypeChecker`，不改内核行为
- 逐步展示 β/δ 归约（教学核心价值），老项目"卡死"由 `CheckTimeoutError` 兜底

## 范围（v1）

- `#check <e>` / 直接输入表达式 → 显示类型（含 sort 层级）
- `#reduce <e>` → 逐步 β/δ 归约序列
- `#print <name>` → 打印常量完整类型/定义
- `#env` → 列出内置常量；`#help`；`#quit`/Ctrl-D
- 表达式输入用 Lean 风格子集语法（fun/∀/应用/@显式隐式参数/Nat 字面量）
- CLI：`py-nanobruijn repl` 子命令（`check`/`inspect` 保持不动）

不在 v1：infer 推导树逐步 hook（需给 `_infer_*` 加回调）、隐式参数自动填充
（内核无 metavariable）、外部 export 加载。

## 架构

新增子包 `py_nanobruijn/teaching/`，复用 `TcCtx`/`TypeChecker`/`Env`/`LeanDag`。
内核零改动（不加 hook），逐步归约通过镜像 `whnf_inner` 主循环、复用内核原语实现。

### 文件组织

```
py_nanobruijn/
  teaching/
    __init__.py
    core.py     # 内置逻辑核心：Python 构造器 → Env
    lexer.py    # Lean 子集 tokenizer
    parser.py   # 表达式 parser → ExprPtr
    pretty.py   # ExprPtr → Lean 语法字符串
    reduce.py   # 逐步归约驱动
    repl.py     # REPL 主循环 + 命令分发
  test_teaching.py   # 单元测试（pytest，包根下，沿用现有惯例）
__main__.py          # 加 repl 子命令
```

## 组件设计

### 1. 内置逻辑核心（teaching/core.py）

用 `ctx.mk_*` + dag API 直接构造 `Declar` 并组装 `Env`，不走 NDJSON parser。

- Axiom（不可 δ 展开）：`True`/`True.intro`、`False`/`False.rec`、`Eq`/`Eq.refl`/
  `Eq.rec`、`HEq`/`HEq.refl`、`And`/`And.intro`/`And.left`/`And.right`、
  `Or`/`Or.inl`/`Or.inr`/`Or.rec`、`Iff`/`Iff.intro`/`Iff.mp`/`Iff.mpr`、
  `Not`（=`fun a : Prop => a -> False`）、`propext`（axiom，unsafe 允许）
- Definition（可 δ 展开，教学演示）：`id`、`Function.comp`、`flip`、
  `Nat.add`（简单递归定义）
- 构造：`TcCtx(LeanDag.with_capacity(config, 0))` → 依次 `insert_name`/
  `insert_level`/`mk_*` 构造 Expr → 组装 `Axiom`/`Definition` → `Env(declars=...)`
- 提供 `BootstrapCore` 类：`ctx`、`env`、`dag`、`name_to_string` 等

### 2. 表达式解析器（teaching/lexer.py + teaching/parser.py）

Lean 风格子集，递归下降 + Pratt：

- Token：标识符（点分常量名）、`fun`/`forall`/`∀`、`=>`、`:`、`,`、`(`/`)`、
  `@`、`Type`/`Prop`/`Sort`、Nat 字面量、`->`
- 语法：
  - `fun x : A => e` / `fun x => e` → Lambda（`ctx.mk_lambda`，绑定名插入 dag）
  - `∀ x : A, e` / `forall x : A, e` / `A -> B` → Pi（非依赖 `->` 简写）
  - `@Const` → 显式传全部参数；`Const a b` → 应用
  - `Type`/`Prop` → `ctx.mk_sort(level)`；`Sort u` → 参数层级
  - 自然数 → `ctx.mk_nat_lit`
- 隐式参数不自动填充（内核无 metavariable）；REPL 帮助提示用 `@`
- 自由变量（未绑定标识符）→ 报错并提示可能意图
- 输出 `ExprPtr`（分配进 `TcCtx` 的同一 dag）

### 3. pretty printer（teaching/pretty.py）

`ExprPtr` → Lean 语法字符串：

- 维护名字栈处理 de Bruijn `Var`；`Const` → 点分名字（复用 `name_to_string`）
- `Pi` → `∀ x : A, B`；非依赖简写 `A -> B`
- `Sort 0` → `Prop`，`Sort 1` → `Type`，`Sort u` → `Type u`
- `Lambda` → `fun x => e`；`Let` → `let x := v; e`；`App` → 空格应用
- 隐式参数全显式（`@And a b` 形式），教学透明优先

### 4. 逐步归约（teaching/reduce.py）

镜像 `whnf_inner` 主循环，复用内核原语，不改内核：

```
reduce_steps(e) -> list[Step]:
  cursor = e
  loop:
    r = tc.whnf_no_unfolding(cursor)     # β/let/proj（内核原语）
    unfolded = tc.unfold_def(r)          # δ（内核原语）
    if unfolded: record(cursor -> unfolded, kind="delta"); cursor = unfolded
    else: record(cursor -> r, kind="whnf"); break
```

- `Step`：`(before: ExprPtr, after: ExprPtr, kind: str)`
- 展示用 pretty 打印前后项
- 死循环由 `TcCtx.check_timeout()`/`timeout_secs` 兜底 → `CheckTimeoutError` →
  REPL 友好提示
- `#check` 显示 `infer` 最终类型（`infer_then_whnf` 或 `infer` + `ensure_sort` 摘要）

### 5. REPL（teaching/repl.py）

- 命令分发：表达式（#check）/ `#reduce` / `#print` / `#env` / `#help` / `#quit`
- 错误友好化：`ValueError`/`CheckTimeoutError` → 一行错误（无 traceback），
  `-v`/`--traceback` 显示完整
- 启动 banner：内置核心版本、常量数量、`#help` 提示
- 输入循环：`input()`，EOF（Ctrl-D）退出；`#quit`/`exit` 退出
- 每个表达式用新的 `TypeChecker`（干净缓存 + timeout）
- CLI 集成：`__main__.py` 加 `repl` 子命令（无输入文件参数）

### 6. 测试（test_teaching.py）

- parser：`parse("fun x => x")` → pretty 往返；错误语法（未闭合括号、
  自由变量）报错
- 内置核心：每个常量可 `infer`；`#print` 输出正确
- reduce_steps：`(fun x => x) True.intro` → `True.intro`；`id True.intro` → δ 步骤
- REPL：`io.StringIO` 模拟输入断言输出
- 全量 pytest 回归：现有 189 测试不受影响