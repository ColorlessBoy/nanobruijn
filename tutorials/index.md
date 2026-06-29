# 📘 py_nanobruijn 核心知识教程

本教程系列从 `py_nanobruijn` 的 Python 源码出发，逐步深入 Lean 4 类型检查器的核心数据结构与算法。

## 📖 学习路径

### 第一部分 数据结构基础

[**Name — 名字系统**](./name) — `name.py`
:   Name 的树状结构和三种变体，hash-consing 机制

[**Level — 宇宙层级**](./level) — `level.py` · `level_ops.py`
:   Level 的五种变体、simplify 和 leq 算法

[**Expr — 表达式 DAG**](./expr) — `expr.py` · `ptr.py` · `tc_context.py`
:   10 种表达式变体、ExprPtr 指针、OSNF 构造器、核心操作

### 第二部分 类型检查算法

[**WHNF — 弱头范式**](./whnf) — `tc_whnf.py`
:   TypeChecker 类、whnf 主循环、β/δ 归约、缓存策略

[**Infer — 类型推断**](./infer) — `tc_infer.py`
:   按标签分发的类型推断、Pi 宇宙计算

[**DefEq — 定义性等价**](./defeq) — `tc_defeq.py`
:   比较流程、Union-Find、Lazy Delta、η 展开

[**TcCache — 缓存系统**](./cache) — `tc_cache.py`
:   缓存分区、DepthFrame、push_local/pop_local、split_off/extend

### 第三部分 前端与顶层编排

[**Parser — 导出文件解析**](./parser) — `parser.py`
:   NDJSON 反序列化、remap 机制、OSNF 优化、声明解析

[**Env — 环境系统**](./env) — `env.py`
:   ReducibilityHint、数据类、Declar 层次、cutoff 可见性控制

[**Inductive — 归纳类型检查**](./inductive) — `inductive.py`
:   互递归块、构造器 target 验证、recursor telescope 校验

[**check_decl — 声明检查**](./check_decl) — `check_decl.py`
:   声明分派、公共验证、EnvLimit、批量编排

### 第四部分 运行与测试

[**运行与测试**](./running) — `__main__.py` · `config.py` · `test_*.py`
:   CLI 入口、Config 配置、测试体系、完整工作流

## 🗺️ 模块依赖关系

```
Lean 源文件
    ↓  (编译)
.export 文件 (NDJSON)
    ↓
Parser  ←  name / level / expr remap
    ↓
ExportFile (declars, dag, config)
    ↓
Env (cutoff, temp_declars, 声明查找)
    ↓
TypeChecker ─── TcCache（缓存）
    ├── WHNF
    ├── Infer
    ├── DefEq
    └── Inductive / check_decl
    ↓
结果通过/失败
```
