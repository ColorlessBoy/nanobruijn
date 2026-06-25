# Tutorials Restructure Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Split `tutorials/learn_name_level.html` into `index.html` + `style.css` + `script.js` with improved content organization.

**Architecture:** One directory `tutorials/learn_name_level/` containing three files. CSS and JS extracted verbatim from the original single file. `index.html` rewritten with restructured content sections (导言 → Name → Level → 结语) while keeping the tab-based UI.

**Tech Stack:** Vanilla HTML/CSS/JS (no frameworks, no build tools, no server needed).

## Global Constraints

- CSS must be copied verbatim from original `<style>` — no visual changes
- JS must be copied verbatim from original `<script>` — no behavior changes
- All interactive demos (name tree, simplify, leq) must work identically
- Must work when opened as `file://` (relative paths for CSS/JS)
- Original `tutorials/learn_name_level.html` left untouched
- Content additions: only 要点总结 cards, transition hints, 导言, and 结语

---

### Task 1: Extract CSS

**Files:**
- Create: `tutorials/learn_name_level/style.css`
- Source: `tutorials/learn_name_level.html` lines 8-109

- [ ] **Step 1: Create directory and extract CSS**

```bash
mkdir -p tutorials/learn_name_level
```

Extract lines 8-109 from the original HTML file into `style.css`, removing only the outer `<style>` tags.

- [ ] **Step 2: Verify extraction**

```bash
wc -l tutorials/learn_name_level/style.css
# Expected: ~102 lines (lines 8-109 minus 2 style tags = 100-102 lines)
head -3 tutorials/learn_name_level/style.css
# Expected: starts with CSS content, no <style> tag
```

### Task 2: Extract JS

**Files:**
- Create: `tutorials/learn_name_level/script.js`
- Source: `tutorials/learn_name_level.html` lines 487-867

- [ ] **Step 1: Extract JS from original HTML**

Extract lines 487-867 from the original HTML file into `script.js`, removing only the outer `<script>` tags. Content includes:
- Tab switching (`switchTab`)
- Name tree rendering (`NAME_TREE`, `renderNameTree`)
- Level definitions (`LEVELS`)
- Level utility functions (`levelToString`, `levelToShort`, `levelToMath`, `levelToExpr`, `cloneLevel`)
- Simplify algorithm (`simplifyLevelPure`, `simplifyLevelWithSteps`, `isZero`, `isOne`, `combining`)
- leq algorithm (`leq`, `runSimplify`, `runLeq`)
- Initialization code

- [ ] **Step 2: Verify extraction**

```bash
wc -l tutorials/learn_name_level/script.js
# Expected: ~381 lines (lines 487-867 minus 2 script tags)
```

### Task 3: Write restructured `index.html`

**Files:**
- Create: `tutorials/learn_name_level/index.html`

**Content organization:**

```
导言 (new — 1 paragraph) →
Tab bar (Name | Level) ⬅ kept from original
  Tab 1: Name
    - 1.1 名字 = 带路径前缀的树 (original)
    - 1.2 名字树交互可视化 (original)
    - 1.3 三种变体卡片 (original)
    - 1.4 代码对照: name.py (original)
    - 1.5 要点总结 (new card)
    - → 过渡提示: "下一站: Level"
  Tab 2: Level
    - 2.1 宇宙层级 (original Sort chain)
    - 2.2 五种变体卡片 (original)
    - 2.3 Pi 类型宇宙规则 (original)
    - 2.4 simplify 交互演示 (original)
    - 2.5 leq (original: what + diff + rules + demo + code)
    - 2.6 代码挂接方式 (original)
    - 2.7 要点总结 (new card)
    - → 过渡提示
结语 (new — 2-3 sentences)
```

- [ ] **Step 1: Write HTML structure with new content flow**

Structure:
```html
<!DOCTYPE html>
<html lang="zh-CN">
<head>
  <meta charset="UTF-8">
  <meta name="viewport" content="width=device-width, initial-scale=1.0">
  <title>Lean 4 Kernel 入门 — Name & Level</title>
  <link rel="stylesheet" href="style.css">
</head>
<body>
<div class="container">

  <!-- 导言 -->
  <h1>📐 Lean 4 Type Checker 入门</h1>
  <p>从 py_nanobruijn 代码出发，理解 Name 和 Level 这两个最基础的数据结构。...</p>

  <!-- Tab bar (same as original) -->
  <div class="tab-bar">...</div>

  <!-- Tab: Name (same content + 要点总结 cards + transition) -->
  <div id="tab-name" class="tab-content active">...</div>

  <!-- Tab: Level (same content + 要点总结 + transition) -->
  <div id="tab-level" class="tab-content">...</div>

  <!-- 结语 -->
  <div class="card">...</div>

</div>
<script src="script.js"></script>
</body>
</html>
```

- [ ] **Step 2: Add 导言 section**

Insert before the tab bar. Content:
```html
<p style="font-size:1.1rem; margin-bottom:2rem;">
  从 <code>py_nanobruijn</code> 代码出发，理解 Name（名字）和 Level（宇宙层级）这两个最基础的数据结构。
  掌握它们，就为理解表达式结构（Expr）、类型推断和 WHNF 算法打下基础。
</p>
```

- [ ] **Step 3: Add 要点总结 cards**

Inside the Name tab, after the code card:
```html
<div class="card">
  <div class="card-title"><span class="badge b-green">✓ 要点总结</span></div>
  <ul style="list-style:none;padding:0;">
    <li>• Name 是带路径前缀的树状结构，支持 hash-consing</li>
    <li>• 三种变体：<code>Anon</code>（匿名）、<code>Str</code>（字符串名）、<code>Num</code>（数字后缀）</li>
    <li>• <code>Name.Str(pfx, sfx)</code> 构成 <code>Nat.add</code> 这样带路径的名字</li>
  </ul>
</div>
```

Inside the Level tab, before the footnote:
```html
<div class="card">
  <div class="card-title"><span class="badge b-green">✓ 要点总结</span></div>
  <ul style="list-style:none;padding:0;">
    <li>• Level 是描述宇宙层级的表达式，<code>Zero</code> = Prop, <code>Succ(Zero)</code> = Type</li>
    <li>• <code>IMax</code> 实现非直谓性：v=0 → 0, v≠0 → Max(u, v)</li>
    <li>• <code>simplify</code> 去掉冗余的 Max/IMax 嵌套</li>
    <li>• <code>leq</code> 用 diff 追踪后继差，递归比较层级大小</li>
  </ul>
</div>
```

- [ ] **Step 4: Add 结语 section**

After the Level tab, before the footnote:
```html
<div class="card" style="margin-top:2rem;">
  <div class="card-title">📚 下一步</div>
  <p>
    理解了 Name（名字系统）和 Level（宇宙层级），你就掌握了 py_nanobruijn
    的两个核心基础模块。接下来可以深入 <strong>Expr</strong>（表达式结构）、
    <strong>WHNF</strong>（弱头范式）和 <strong>type inference</strong>
    （类型推断算法），理解整个类型检查器如何工作。
  </p>
</div>
```

- [ ] **Step 5: Add transition hints**

After the Name section summary card:
```html
<p style="text-align:right;color:#8b949e;font-size:0.9rem;">
  <a href="javascript:switchTab('level')" style="color:#58a6ff;">→ 下一节：Level — 宇宙层级</a>
</p>
```

### Task 4: Verification

- [ ] **Step 1: Verify file structure**

```bash
ls -la tutorials/learn_name_level/
# Expected: index.html, style.css, script.js
```

- [ ] **Step 2: Verify CSS content matches**

```bash
diff <(sed -n '8,109p' tutorials/learn_name_level.html | sed '1d;$d') tutorials/learn_name_level/style.css
# Expected: no differences (after stripping <style> tags)
```

- [ ] **Step 3: Verify JS content matches**

```bash
diff <(sed -n '487,867p' tutorials/learn_name_level.html | sed '1d;$d') tutorials/learn_name_level/script.js
# Expected: no differences (after stripping <script> tags)
```

- [ ] **Step 4: Manual browser check**
  - Open `tutorials/learn_name_level/index.html` in browser
  - Confirm page renders with correct dark theme
  - Click Name tab → confirm name tree expands/collapses
  - Click Level tab → confirm all content visible
  - Test simplify demo: select expressions → confirm simplification output
  - Test leq demo: change LV/RV selectors → confirm result and trace
