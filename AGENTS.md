# nanobruijn

nanobruijn 是 Lean 4 内核类型检查器的研究实现：Rust 版（`src/`，fork 自
nanoda_lib）+ Python 移植（`py_nanobruijn/`）+ 教学 REPL（`py_nanobruijn/teaching/`）。
核心设计：纯 de Bruijn 索引 + shift-homomorphic 缓存（`ExprPtr = (core, shift)`）、
解析期 OSNF 归一化。详见 `README.md` 与 `PLAN.md`。

## 构建与测试

```bash
# Python（唯一活跃开发目标）
.venv/bin/python -m pytest py_nanobruijn -q   # 全量测试（当前 316 个）
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
    game.py                                         # GameLoader + GameSession（.game 关卡 + 星级/存档）
  worlds/*.game                                     # 6 个闯关世界（And/Or/Not/Exists/Iff/Combo）
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
  `#print <name>` / `#prove <类型>`（tactic 草稿）/ `#env` / `#help` / `#quit`；
  每行新 `TypeChecker`（`--timeout` 防卡死）
- CLI：`repl --script "<行1>|<行2>"` 非交互执行；`--json` 输出机器可读 JSON
  （agent 集成）；`--game <世界>` 启动即进入闯关世界
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

## GAME 模式（闯关世界，py_nanobruijn/teaching/game.py + worlds/）

- 6 个世界：And/Or/Not/Exists/Iff/Combo（各 5 关，见 `worlds/*.game`）；
  启动：`repl --game <世界>`，或 REPL 内 `#game <世界>` / `#worlds`（列出全部与完成度）
- 关卡内（`proof>` 提示符）额外命令：`hint`（逐条提示，用一次即降星）/
  `solution`（显示标准解并放弃本关）；tactic 前导 `abort` 退出关卡回主 REPL
- 星级（`GameSession.complete`）：3★ = 无 hint 且步数 ≤ 标准解行数；2★ = 无 hint；
  1★ = 其余；步数只计 STEP_TACTICS（intro/apply/exact/cases）；`ban:` 字段禁用的
  tactic 直接拒绝并提示换路
- 存档：`py_nanobruijn/saves/<world_id>.json`（`{"stars": {...}}`，已 gitignore）；
  `GameSession.load_progress` 启动时读取；通关条件 = 每关至少 1★（`next_unfinished`）
- `.game` 格式（行式，`#` 注释）：`world <id>` / `title <标题>` / `intro <叙事>` /
  `level <n>` / `name <关名>` / `goal: <命题>` / `hint: <文本>`（可多个）/
  `ban: <tactic>`（可多个）/ `solution:` 后跟标准解脚本行，`---` 结束（见 game.py docstring）

## 约定

- **内核零改动原则**：教学层及 CLI 增强不得修改 `tc_*.py`/`dag.py`/`env.py`/`parser.py`/
  `expr.py`（只能加 `teaching/` 与 `__main__.py`）——**但真实内核 bug 的修复不在此列**，
  已授权修复（见下）
- 测试单文件 `py_nanobruijn/test_teaching.py`（TestCore/TestParser/TestPretty/TestReduce/
  TestRepl/TestCli 类分组）；fixture 模式见 `test_tc_infer.py`（`make_ctx`/`insert_name`）
- 教学 REPL 的价值是复用真实内核：改动优先复用 `TcCtx`/`TypeChecker` 原语，
  逐步归约用 `whnf_no_unfolding` + `unfold_def` 镜像 `whnf_inner` 主循环

## 已知内核问题与修复记录（Python 移植 vs Rust 参考实现）

- **已修复**（b784124）：`tc_cache.push_local`/`push_local_let` 帧复用缺失 Rust 的
  类型匹配条件（`src/util.rs`：类型不匹配即 truncate；Python 移植只查深度导致陈旧
  缓存污染 sibling lambda）——修复后 `and_comm` 等定理通过
- **已修复**（b784124）：教学层 `parse_arrow` 的 `A -> B` body 未提升 1 层（匿名
  binder 内变量引用错位）——修复后 `@Iff.intro (a -> b) (b -> a)` 可检查
- **已修复**（b784124）：`pretty._pp_sort` 对 IMax/Max level 打印 `Type -1`
  （unwrap 归零未回检）——改为内核 `simplify` 归一化
- **已修复**（73bb895）：`True.intro` 的类型被错误声明为 `Prop`（应为 `True` 常量）
  ——"良类型但语义错位"的一类（check 模式只验证良类型）
- **已修复**（53bddaa）：`imp.swap` 的 `b -> a -> c` 内层 binder 类型深度错误
  （var2 应为 var3）——同类语义错位；修复后 14/14 定理通过严格验证
- **已修复**（52acafd）：`cases` tactic 的 rec 应用/分支 binder 深度硬编码
  shift 1/2（`proof.py`），当被分解的 `h` 不是最内层 binder（h_idx > 0）时
  shift 不足导致变量引用错位——改为 `1 + h_idx`/`2 + h_idx` 后
  `cases` 在任意上下文深度可用（Game 模式 Exists/Combo 世界依赖此修复）
- **防护**（53bddaa）：`test_core_semantic_parity`——核心常量类型 vs 教学 parse
  等价表达式的内核 def_eq 比较，防止"良类型但语义错位"回归（该测试正是发现
  imp.swap 深度错误的手段；修改常量类型构造后必须保持此测试全绿）