# nanobruijn

nanobruijn 是 Lean 4 内核类型检查器的研究实现：Rust 版（`src/`，fork 自
nanoda_lib）+ Python 移植（`py_nanobruijn/`）+ 教学 REPL（`py_nanobruijn/teaching/`）。
核心设计：纯 de Bruijn 索引 + shift-homomorphic 缓存（`ExprPtr = (core, shift)`）、
解析期 OSNF 归一化。详见 `README.md` 与 `PLAN.md`。

## 构建与测试

```bash
# Python（唯一活跃开发目标）
.venv/bin/python -m pytest py_nanobruijn -q   # 全量测试（当前 242 个）
.venv/bin/ruff check py_nanobruijn            # lint（line-length 100, py310）

# Rust（参考实现，非活跃）
cargo build --release
```

提交前必须：`pytest py_nanobruijn -q` 全绿 + `ruff check py_nanobruijn` 0 errors。

## 架构（Python 版）

```
py_nanobruijn/
  dag.py / name.py / level.py / expr.py / ptr.py   # hash-consing DAG + 表示层
  parser.py / env.py / config.py                    # NDJSON export 解析
  tc_context.py / tc_whnf.py / tc_infer.py /
  tc_defeq.py / tc_cache.py / level_ops.py          # 内核：whnf/infer/def_eq
  inductive.py / quot.py / check_decl.py            # 声明检查
  services/checker.py / results.py / api.py         # 编排层 + CLI 支撑
  __main__.py                                       # CLI: check / inspect / repl
  teaching/                                         # 教学 REPL（见下）
```

内核约定（重要）：
- 类型错误一律抛 `ValueError`（`errors.py` 的 KernelError 实际不抛）；超时抛 `CheckTimeoutError`
- `Env` 的 `cutoff` 在构造时按 `len(declars)` 计算——事后填充 `env.declars` 必须手动刷新 `env.cutoff`
- `dag.uparams[ptr]` 存的是 **LevelPtr**（不是 NamePtr）；`insert_uparams` 接收 level 指针元组
- `unfold_def` 只在常量应用处 level 参数数量与声明 uparams 数量相等时展开（`tc_whnf.py:100`）
- Pi/Lambda 节点：`binder_type` 位于 binder 之外（深度 d），`body` 位于深度 d+1；
  表达式位于第 k 层 binder 之下时，最内层 binder 是 var 0
- 无 `get_string`/`get_bignum`——用列表属性 `dag.strings[ptr]` / `dag.bignums[ptr]`
- NatLit 类型推断是死路径（`tc_infer.py` 需要 `ctx.export_file.config.nat_extension`，
  直接构造的 `TcCtx` 没有）——教学 REPL 对 `#check` 含 NatLit 的表达式做了友好拦截

## 教学 REPL（py_nanobruijn/teaching/）

```bash
.venv/bin/python -m py_nanobruijn repl        # 或 py-nanobruijn repl
```

- 内置逻辑核心（`core.py`，21 个常量）：True/False/And/Or/Iff/Eq/propext/Not/id/
  Function.comp/flip——用 Python 构造器直接组装 `Env`，不依赖 NDJSON export
- 命令：`#check <e>`（默认，直接输入表达式）/ `#reduce <e>`（逐步 β/δ 归约）/
  `#print <name>` / `#env` / `#help` / `#quit`；每行新 `TypeChecker`（`--timeout` 防卡死）
- 语法：`fun (x : A) => e`、`∀ (x : A), e`、`A -> B`、`@Const`、`Type`/`Prop`/`Sort u`、
  `id.{u}`（universe 实例化，见下）、Nat 字面量
- **binder 必须带类型注解**（内核 Lambda 需要 binder_type，无 metavariable）：
  `fun x => e` 会报 ParseError
- 隐式参数不自动填充：`@And True True` 显式传全部参数
- pretty 规则：命名 binder 显示 `∀ (x : A), B`（不简写箭头）；箭头简写只用于解析器
  合成的匿名 binder；首 binder 为 IMPLICIT 的常量打印 `@Const ...`
- 常量带 universe 参数时：不带 `.{...}` 默认实例化为 0（Prop 层）；`id.{u}`/`id.{0}`/
  `Function.comp.{u, v, w}` 显式实例化；数量不符或无 uparams 的常量带 `.{...}` 报 ParseError；
  `id.{u} True` 会类型错误（内核无 elaboration，Sort u ≠ Prop 即正确语义）

## 约定

- **内核零改动原则**：教学层及 CLI 增强不得修改 `tc_*.py`/`dag.py`/`env.py`/`parser.py`/
  `expr.py`（只能加 `teaching/` 与 `__main__.py`）
- 测试单文件 `py_nanobruijn/test_teaching.py`（TestCore/TestParser/TestPretty/TestReduce/
  TestRepl/TestCli 类分组）；fixture 模式见 `test_tc_infer.py`（`make_ctx`/`insert_name`）
- 教学 REPL 的价值是复用真实内核：改动优先复用 `TcCtx`/`TypeChecker` 原语，
  逐步归约用 `whnf_no_unfolding` + `unfold_def` 镜像 `whnf_inner` 主循环