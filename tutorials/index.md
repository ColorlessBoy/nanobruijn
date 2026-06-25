# 📘 py_nanobruijn 核心知识教程

本教程系列从 `py_nanobruijn` 的 Python 源码出发，逐步深入 Lean 4 类型检查器的核心数据结构与算法。

## 📖 学习路径

### 第一章 数据结构基础

[**Name — 名字系统**](./name) — `name.py`
:   Name 的树状结构和三种变体，hash-consing 机制

[**Level — 宇宙层级**](./level) — `level.py` · `level_ops.py`
:   Level 的五种变体、simplify 和 leq 算法

[**Expr — 表达式 DAG**](./expr) — `expr.py` · `ptr.py` · `tc_context.py`
:   10 种表达式变体、ExprPtr 指针、OSNF 构造器、核心操作

### 第二章 类型检查算法

[**WHNF — 弱头范式**](./whnf) — `tc_whnf.py`
:   TypeChecker 类、whnf 主循环、β/δ 归约、缓存策略

[**Infer — 类型推断**](./infer) — `tc_infer.py`
:   按标签分发的类型推断、Pi 宇宙计算

[**DefEq — 定义性等价**](./defeq) — `tc_defeq.py`
:   比较流程、Union-Find、Lazy Delta、η 展开

## 🗺️ 模块依赖关系

```
name → level → expr → env → parser
  ↘      ↘        ↘        ↘
    ← dag / ptr / TcCtx / ExportFile →
                    ↓
              TypeChecker
              /    |     \
          WHNF  Infer  DefEq
```
