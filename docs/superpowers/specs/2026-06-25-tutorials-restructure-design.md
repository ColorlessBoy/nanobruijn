# Tutorials Restructure — Name & Level

## Goal

Refactor `tutorials/learn_name_level.html` into a multi-file structure with
improved content organization, keeping all existing content and interactive
functionality unchanged.

## Scope

Two changes only:

1.  **File splitting** — monolithic HTML → `index.html` + `style.css` + `script.js`
2.  **Content reorganization** — better learning path without changing any
    explanatory text, code snippets, or interactive demos.

## File Structure

```
tutorials/
  learn_name_level/             # new directory
    index.html                  # HTML structure
    style.css                   # all CSS (copied from <style>)
    script.js                   # all JS (copied from <script>)
```

- `tutorials/learn_name_level.html` is left untouched (can be deleted later).
- CSS and JS extracted verbatim from the original single file.
- `index.html` links to `style.css` via `<link>` and `script.js` via `<script>`.

## Content Organization

### Learning path

```
导言 → Name 章节 → Level 章节 → 结语
```

Replaces the current flat two-tab layout with a sequential narrative flow
while keeping the tab-based UI (Name tab / Level tab) as section navigation.

### Sections

#### 导言 (new)

Brief paragraph setting context:
- What is py_nanobruijn / nanobruijn
- Why Name and Level are foundational
- How this tutorial connects to `py_nanobruijn/name.py` and `level.py`/`level_ops.py`

#### 1. Name — 名字系统

1.1 名字 = 带路径前缀的树 (existing)
1.2 名字树交互可视化 (existing, name tree widget)
1.3 三种变体卡片 (existing: Anon, Str, Num)
1.4 代码对照: `name.py` 简化版 (existing)
1.5 **要点总结** (new card)
     → 过渡提示: "下一站：Level — 宇宙层级"

#### 2. Level — 宇宙层级

2.1 什么是宇宙层级 — Sort 层级链 (existing)
2.2 五种变体卡片 (existing: Zero, Succ, Max, IMax, Param)
2.3 Pi 类型的宇宙规则 — IMax 详解 (existing)
2.4 核心算法: simplify — 交互演示 (existing)
2.5 核心算法: leq
     - leq 在问什么 (existing)
     - diff 概念解释 (existing)
     - 递归规则表 (existing)
     - 交互演示 (existing)
2.6 代码挂接方式 — monkey-patch (existing)
2.7 **要点总结** (new card)
     → 过渡提示: "下一站可以深入 Expr / WHNF / infer"

#### 结语 (new)

Brief closing paragraph summarizing the journey from Name to Level and pointing
to the next topics in py_nanobruijn (Expr, WHNF, type inference).

### New elements

- **要点总结卡片**: 一个 `.card` 用 `.b-green` badge，列出本小节关键概念
- **过渡提示**: 每节末尾一行文字，引导读者到下一节
- **结语**: 3-4 句总结 + 下一步方向

## Design Constraints

- All interactive demos (name tree, simplify, leq) must work exactly as before.
- No CSS changes — visual style (GitHub Dark) preserved exactly.
- No JS logic changes — only code motion.
- No explanatory text removed; only additions are the summary cards and
  transition hints.
- Must work when opened as `file://` (no server needed) — CSS/JS loaded
  relative to HTML file.

## Non-goals

- New interactive features or demo enhancements
- Adding more tutorial topics (Expr, WHNF, etc.)
- Converting to a different format (Markdown, Sphinx, etc.)
- Adding sidebars, table of contents, or glossary
- Changing visual theme

## Verification

After implementation:
- Open `tutorials/learn_name_level/index.html` in browser
- Confirm both tabs work
- Confirm name tree expand/collapse works
- Confirm simplify demo populates and computes
- Confirm leq demo populates and traces
- Run `diff -r` on extracted CSS/JS against original `<style>`/`<script>` to
  ensure no content drift
