# 剩余三讲教程 — 实施计划

> **For agentic workers:** Each task is a tutorial document to write.

**Goal:** 完成 tc_cache（缓存系统）、inductive（归纳类型检查）、测试与运行 三篇教程，覆盖 nanobruijn 源码中尚未专题讲解的全部主要模块。

**计划调整：** 重新划分部分结构，每讲各自归入最合适的位置。

---

### 结构调整

| 部分 | 包含讲次 | 说明 |
|------|---------|------|
| 第一部分 数据结构基础 | 1–3 (Name, Level, Expr) | 不变 |
| 第二部分 类型检查算法 | 4–7 (WHNF, Infer, DefEq, **tc_cache**) | 新增第 7 讲缓存 |
| 第三部分 前端与顶层编排 | 8–11 (Parser, Env, **inductive**, check_decl) | 新增第 10 讲 inductive |
| 第四部分 运行与测试 | 12 (**CLI + Config + 测试**) | 新增第四部分 |

### Task 1: tc_cache — 缓存系统

**目标文件:** `tutorials/cache.md`

**定位:** 第二部分 第 7 讲（紧随 DefEq 之后，因缓存是 WHNF/Infer/DefEq 的公共基础设施）

**内容大纲:**

1. **TcCache 整体结构** — 6 个缓存的映射图（whnf / wnu / infer_check / infer_no_check / defeq_neg / uf）
2. **DepthFrame — 每层 binder 的缓存帧** — push_local / pop_local / restore_depth
3. **Bucket 0 vs Bucket k** — 闭项全局共享 vs 开项按 depth 分区
4. **六种缓存各自用途**：
   - whnf_cache: WHNF 结果
   - wnu_cache: whnf_no_unfolding 结果
   - infer_check / infer_no_check: 类型推断
   - defeq_neg_cache: 不相等结论的负缓存
   - uf_cache: Union-Find 代表元
5. **split_off / extend** — 跨 binder 深度的缓存生命周期管理
6. **与 TypeChecker 的集成** — cache_bucket、whnf_get/insert、split_off 在 whnf_inner 中的协作

**参考代码行:** `py_nanobruijn/tc_cache.py` (225 行)

---

### Task 2: inductive — 归纳类型检查

**目标文件:** `tutorials/inductive.md`

**定位:** 第三部分 第 10 讲（Parser + Env 之后，check_decl 之前——因为归纳检查是 check_decl 委托出去的）

**内容大纲:**

1. **归纳类型声明结构** — InductiveDecl 中的 inductives / constructors / recursors 三元组
2. **`_check_inductive_type`** — 验证归纳类型本身的类型是 Sort
3. **`_check_constructor_type`** — 两步验证：
   - 通过 `check_declar_info` 验证构造器类型是良类型的
   - 通过 `_check_ctor_target_type` 剥离 Pi layers，验证最后落脚点是该归纳类型的应用
4. **`_check_recursor_type`** — telescope 大小校验（params + motives + minors + indices + 1）
5. **互递归块的 temp_declars 机制** — 与 check_decl 中 EnvLimit 的协同
6. **check_inductive_declar 整体流程** — 如何串联类型/构造器/消去子的检查

**参考代码行:** `py_nanobruijn/inductive.py` (171 行)

---

### Task 3: 运行与测试

**目标文件:** `tutorials/running.md`

**定位:** 第四部分 第 12 讲（独立的实操部分）

**内容大纲:**

1. **入口：`python -m py_nanobruijn`** — `__main__.py` 的流程：解析参数 → 逐行 parse → check_all_declars
2. **Config 配置项** — 常用标志速查表（nat/string_extension, permitted_axioms, max_declarations, declaration_timeout_secs 等）
3. **解析流程** — `parse_export_file` → Parser.feed_line → finalize → ExportFile
4. **测试体系** — pytest 结构：test_full_suite.py（集成测试）+ 各模块独立测试
5. **关键测试模式**：
   - `make_ctx()` 辅助建环境
   - 表达式构造辅助函数（insert_name, param_quick, mk_max 等）
   - 测试组织方式
6. **运行示例** — 从 .export 文件到输出结果的全流程命令行示例

**参考代码行:** `py_nanobruijn/__main__.py` (46 行) + `py_nanobruijn/config.py` (59 行) + 各 test_*.py
