# py_nanobruijn

Python 移植的 [nanobruijn](https://github.com/nomeata/nanobruijn) — Lean 4 kernel 类型检查器。

## 架构

```
py_nanobruijn/
├── __init__.py          # 公共导出 + 自动 patch
├── name.py              # Name (Anon/Str/Num)
├── level.py             # Level (Zero/Succ/Max/IMax/Param)
├── expr.py              # Expr (11 个变体)
├── ptr.py               # ExprPtr, CorePtr, LevelPtr 等指针类型
├── binder_style.py      # BinderStyle 枚举
├── dag.py               # LeanDag (hash-consing DAG) + TcCtx
├── env.py               # Declar, DeclarInfo, Env 等声明类型
├── config.py            # Config 配置
├── parser.py            # NDJSON 导出格式解析器
├── level_ops.py         # 宇宙层级操作 (simplify, leq, subst 等)
├── tc_context.py        # TcCtx 表达式操作 (shift, inst, unfold 等)
├── tc_cache.py          # 类型检查缓存
├── tc_whnf.py           # TypeChecker + WHNF 归约
├── tc_infer.py          # 类型推理 (infer, ensure_sort 等)
├── tc_defeq.py          # 定义相等性 (is_def_eq, assert_def_eq)
├── check_decl.py        # 声明检查入口
├── inductive.py         # 归纳类型检查器
├── quot.py              # Quot 声明检查
├── __main__.py          # CLI 入口 (python3 -m py_nanobruijn < file.ndjson)
├── test_*.py            # 测试文件 (共 12 个, 183 个测试)
└── README.md            # 本文件
```

## 依赖关系

```
unique_hasher → name → level → expr → env → parser → tc → inductive/quot
                    ↙           ↙        ↙        ↙         ↙
                 util (Ptr, DAG, TcCtx, ExportFile)
```

## 使用

```bash
# 从文件读取
python3 -m py_nanobruijn < path/to/export.ndjson

# 从 Lean 管道输入
lean --export - MyFile.lean | python3 -m py_nanobruijn

# 运行测试
python3 -m pytest py_nanobruijn/ -v
```

## 从 Rust 移植的关键差异

| Rust | Python |
|---|---|
| `enum` with payloads | `@dataclass` + `match/case` (3.10+) |
| `Ptr<A>` 标记指针 | 直接用整数索引 |
| `ExprPtr(core, shift)` | `(core_idx, shift)` dataclass |
| `IndexSet` hash-consing DAG | `list` + `dict` 实现 |
| 生命周期 / `unsafe` | 无此问题 |
| 性能敏感 | 目标是通过测试 |

## Rlint 状态

- `ruff check`: 0 warnings
- `pytest`: 183/183 passed

## lean-kernel-arena 测试结果

| 测试 | 预期 | 实际 | 大小 |
|------|------|------|------|
| `sparse-name-index` | accept | ✅ accept | 0.3 KB |
| `level-index-out-of-order` | accept | ✅ accept | 0.3 KB |
| `constlevels` | reject | ✅ reject | 15 KB |
| `large-elim-param` | reject | ✅ reject | 3 KB |
| `level-imax-leq` | reject | ✅ reject | 6 KB |
| `level-imax-normalization` | reject | ✅ reject | 6 KB |
| `nat-rec-rules` | reject | ✅ reject | 8 KB |
| `proj-of-prop` | reject | ✅ reject | 4 KB |
| `bogus1` | reject | ✅ reject | 11 KB |
| `k-rec-conv` | reject | ✅ reject | 13 KB |
| `cedar` | accept | ⏱️ timeout | 729 MB |

未测试（build-test 阶段超时）：`cslib`, `init`, `init-prelude`, `std`, `tutorial`, `mathlib`
