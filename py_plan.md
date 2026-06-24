# nanobruijn Python 移植计划

移植目标：将 Lean 4 kernel 类型检查器从 Rust 移植到 Python，通过全部现有测试。

## Rust → Python 关键差异处理

| Rust | Python |
|---|---|
| ADT enum | `@dataclass` + `match/case` (3.10+) |
| `Ptr<A>` 标记指针 | 直接用 Python 对象引用 |
| `ExprPtr(core, shift)` | `(core_idx, shift)` 元组或小 dataclass |
| Hash-consing DAG | `__new__` + `__hash__`/`__eq__` 自动去重，或手工 `LeanDag` |
| 生命周期 / unsafe | 无此问题 |
| 性能敏感 | 目标是通过测试，非处理 Mathlib |

## 模块依赖关系

```
unique_hasher ─→ name ─→ level ─→ expr ─→ env ─→ parser ─→ tc ─→ inductive/quot
                    ↙           ↙        ↙        ↙         ↙
                 util (Ptr, DAG, TcCtx, ExportFile)
```

## 分阶段计划

### Phase 0：基础设施

| 文件 | 内容 |
|---|---|
| `dag.py` | `LeanDag`：带 hash-consing 的 Name/Level/Expr 存储池，`index_of` / `get` |
| `name.py` | `Name`（`Anon`, `Str`, `Num`），实现 `__hash__` / `__eq__` |
| `level.py` | `Level`（`Zero`, `Succ`, `Max`, `IMax`, `Param`） |
| `expr.py` | `Expr`（`Var`, `Sort`, `Const`, `App`, `Pi`, `Lambda`, `Let`, `Proj`, `StringLit`, `NatLit`） |
| `ptr.py` | `ExprPtr(core_idx, shift)`，`CorePtr` 用 `int`（DAG 索引） |
| `binder_style.py` | `BinderStyle` 枚举 |

### Phase 1：解析

| 文件 | 内容 |
|---|---|
| `config.py` | `Config` JSON 反序列化 |
| `parser.py` | NDJSON 格式解析 → `ExportFile` |
| `env.py` | `Declar`, `DeclarInfo`, `InductiveData`, `ConstructorData`, `RecursorData`, `Env` |

### Phase 2：核心类型检查器

| 文件 | 内容 |
|---|---|
| `tc_context.py` | `TcCtx`：表达式操作（inst, shift, abstr 等） |
| `tc_cache.py` | `TcCache`, `DepthFrame`：类型检查缓存 |
| `level_ops.py` | 宇宙层级操作：`simplify`, `subst_level`, `leq`, `is_zero` |
| `expr_ops.py` | 表达式操作：`unfold_apps`, `subst_expr_levels`, `inst_beta` |
| `tc.py` | `TypeChecker`：`infer`, `whnf`, `is_def_eq`, `assert_def_eq` |
| `check_decl.py` | 声明检查入口：`check_declar_shift`, `check_all_declars` |

### Phase 3：归纳类型与 Quot

| 文件 | 内容 |
|---|---|
| `inductive.py` | 归纳类型检查：`check_inductive_declar` |
| `quot.py` | `Quot` 声明检查 |

### Phase 4：可选

| 文件 | 内容 |
|---|---|
| `nanoda_tc.py` | Locally-nameless 类型检查器（第二实现，基准对比） |
| `union_find.py` | 并查集（nanoda_tc 用） |
| `pretty.py` | 反打印回 Lean 语法 |

### Phase 5：测试

- 移植 `src/tests/` 下的 34 个测试
- 用 `pytest` 运行
- 覆盖 `test_resources/` 中的所有导出文件

## 测试用例清单

当前 Rust 测试覆盖：

| 测试文件 | 数量 | 类型 |
|---|---|---|
| `src/tests/util.rs` | 5 | 空文件、索引乱序、稀疏索引、Prop 投影 |
| `src/tests/level.rs` | 13 | 宇宙层级操作 |
| `src/tests/natlit.rs` | 16 | Nat 字面量扩展 |

共计 34 个测试。
