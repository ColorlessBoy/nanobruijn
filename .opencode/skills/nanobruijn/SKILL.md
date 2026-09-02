---
name: nanobruijn
description: "Verify Lean proofs and grade student submissions with the nanobruijn teaching REPL. Check proof terms, load game levels, and grade proofs via `py-nanobruijn repl --script`. Use for Lean teaching tasks."
---

# nanobruijn 教学 REPL 驱动

用 `py-nanobruijn repl --script` 无状态验证证明（每行新 TypeChecker，适合 agent 调用）。

## 调用规则

| 任务 | 命令 |
|---|---|
| 验证表达式的类型 | `py-nanobruijn repl --script "#check <expr>"` |
| 批改学生证明（#prove 草稿） | `--script` 传 `#prove <命题>` + 每行一个 tactic + `done` |
| 查常量/定理 | `--script "#print <name>"`（axiom/def/theorem 及其值） |
| 游戏关卡可解性 | `--script` 先 `#game <世界> <关卡号>`（定位到具体关）再传该关标准解——注意会写入 `py_nanobruijn/saves/`（有状态），想干净验证先删对应存档 |
| 机器可读输出 | 加 `--json`（{"ok": bool, "output": str}），错误时返回码非 0 |

## 工作流

1. 学生提交证明（文本）→ 包成 `#prove` + tactic 序列 → `--script --json`
2. 读 `ok` 与 `output`：`内核检查: 通过` = 证明正确；`error:` 行 = 失败原因
3. 反馈循环：把 error 信息转成教学提示（提示用中文，指向下一个该用的 tactic）
4. 多轮批改：每次都是新的 `--script` 调用（无状态）

## Anti-patterns

| ❌ 不要 | ✅ 要 |
|---|---|
| 启动交互式 repl（会挂起等输入） | 永远 `--script`（EOF 自动退出） |
| 猜表达式类型 | 先 `#check` |
| 用内核 `check` 命令跑教学表达式 | 走 `repl`（有 NatLit 拦截等友好错误） |
| 让学生用 `h.1`/`h.2` 投影 | 教学语法用 `And.left`/`And.right` |
| 忘 binder 注解写 `fun x => e` | `fun (x : A) => e`（内核要求） |

## 已知限制

- Nat 字面量（如 `#check 42`）v1 教学核心不支持
- 隐式参数不自动填充：`@And True True` 显式传参
- `Prop : Sort 1`：Exists 需 `@Exists.{1} Prop p`
- 超时保护：默认 5.0s，大项加 `--timeout`
