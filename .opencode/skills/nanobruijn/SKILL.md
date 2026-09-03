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
| 空环境体验 | `--fresh`（`--game` 隐含）：从零开始，进世界时"定义仪式"现场加载 fol 片段 |

## 工作流

1. 学生提交证明（文本）→ 包成 `#prove` + tactic 序列 → `--script --json`
2. 判读三态（output 全文在 json 里，只 grep 关键行）：
   - `内核检查: 通过` 出现且 `ok: true` → 一次做对，肯定
   - `内核检查: 通过` 出现但 `ok: false` → **最终正确但过程中有 error**——
     批改时指出中间的错误行（学生已自我修正，值得肯定 + 提示）
   - 无 `内核检查: 通过` → 未完成，找最后一条 `error:` 行转教学提示
3. 反馈循环：把 error 信息转成中文教学提示（指出目标状态与下一步 tactic）
4. 多轮批改：每次都是新的 `--script` 调用（无状态）
5. 学习产物：退出自动生成 `py_nanobruijn/reports/*.md`（学习报告）；同关连错 3 次
   会交互询问上报（`feedback/*.json`）——`--script` 模式不询问但错误仍入报告

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
