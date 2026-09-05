// nanobruijn 证明游戏 —— Web 前端（TypeScript）
// RPC 契约见 teaching/web_server.py（路线①：Python 服务 + TS 客户端；
// 内核后续可平滑切换为 Rust-WASM，协议不变）。

interface Ctx { context: [string, string][]; goal: string; term: string; note?: string }
interface LevelPayload {
  number: number; name: string; goal: string; bans: string[]; context: Ctx;
}
interface WorldInfo {
  id: string; index: number; title: string; requires: string[];
  done: number; total: number; stars: number[];
}
interface DemoStep { line: string; context?: Ctx; done?: string }
interface EnterResp {
  kind: "entered"; world: string; title: string; intro: string;
  definitions: string; lessons: string[]; example: { goal: string; steps: DemoStep[] };
  level: LevelPayload;
}
interface TacticResp {
  kind: "ok" | "error" | "completed" | "abandoned";
  message?: string; context?: Ctx; output?: string; stars?: number;
  solution?: string[]; variants?: string[]; next?: LevelPayload;
  next_world?: string | null; world_done?: boolean; world?: string;
}
interface HintResp { kind: "hint" | "error"; hint?: string; index?: number;
  total?: number; message?: string }
interface SolutionResp { kind: "solution" | "error"; solution?: string[];
  note?: string; message?: string }
interface WorldsResp { kind: string; worlds: WorldInfo[]; profile: string }

const $ = (id: string): HTMLElement => {
  const el = document.getElementById(id);
  if (!el) throw new Error(`missing #${id}`);
  return el;
};

function esc(s: string): string {
  return s.replace(/&/g, "&amp;").replace(/</g, "&lt;").replace(/>/g, "&gt;");
}

function stars(n: number): string {
  let out = "";
  for (let i = 1; i <= 3; i++) out += `<span class="${i <= n ? "on" : "off"}">★</span>`;
  return `<span class="stars">${out}</span>`;
}

async function rpc(action: string, params: Record<string, unknown> = {}): Promise<any> {
  const res = await fetch("/api", {
    method: "POST",
    headers: { "Content-Type": "application/json" },
    body: JSON.stringify({ action, params }),
  });
  return await res.json();
}

// ---------- 全局状态 ----------

let worlds: WorldInfo[] = [];
let current: EnterResp | null = null;
const tacticHistory: string[] = [];
let historyIdx = 0;

// ---------- 侧边栏 ----------

function renderSidebar(): void {
  const nav = $("world-list");
  nav.innerHTML = "";
  for (const w of worlds) {
    const b = document.createElement("button");
    b.className = "world-item" + (current && current.world === w.id ? " active" : "")
      + (w.done === w.total ? " done-all" : "");
    const dotStars = w.stars.map(s => stars(s)).join("");
    b.innerHTML = `<span class="w-progress">${"①②③④⑤⑥⑦⑧⑨⑩⑪"[w.index - 1] || w.index}`
      + ` ${esc(w.id)}（${w.done}/${w.total}）</span>`
      + `<span class="w-title">${esc(w.title)}</span>`
      + `<span class="w-title">${dotStars}</span>`;
    b.onclick = () => enterWorld(w.id, false);
    nav.appendChild(b);
  }
  renderConsts();
}

function renderConsts(): void {
  const nav = $("const-list");
  const q = ($("const-search") as HTMLInputElement).value.trim().toLowerCase();
  nav.innerHTML = "";
  rpc("constants").then((r: any) => {
    for (const c of r.constants as string[]) {
      if (q && !c.toLowerCase().includes(q)) continue;
      const b = document.createElement("button");
      b.className = "const-item";
      b.textContent = c;
      b.onclick = () => runConsole(`#print ${c}`);
      nav.appendChild(b);
    }
  });
}

// ---------- 世界视图 ----------

async function enterWorld(id: string, replay: boolean): Promise<void> {
  const r: any = await rpc("enter_world", { world: id, replay });
  if (r.kind === "error") { alert(r.message); return; }
  current = r as EnterResp;
  renderSidebar();
  renderWorld();
}

function renderWorld(): void {
  if (!current) return;
  const m = $("main");
  m.innerHTML = `
    <a class="back" id="back-link">← 世界列表</a>
    <h1>${esc(current.title)}</h1>
    <p class="intro">${esc(current.intro)}</p>
    <details class="defs card"><summary>📜 定义仪式（本次加载的声明）</summary>
      <pre>${esc(current.definitions) || "（全部常量已在环境中）"}</pre></details>
    <div class="card" id="lesson-card"></div>
    <div class="card" id="demo-card"></div>
    <div class="card" id="level-card"></div>`;
  $("back-link").onclick = () => { current = null; renderSidebar(); renderWelcome(); };

  const lc = $("lesson-card");
  lc.innerHTML = "<h2>📖 课堂</h2>" + current.lessons
    .map(p => `<p class="lesson-p">${esc(p)}</p>`).join("");

  renderDemo($("demo-card"), current.example);
  renderLevel($("level-card"), current.level);
  m.scrollTop = 0;
}

function renderDemo(el: HTMLElement, demo: { goal: string; steps: DemoStep[] }): void {
  if (!demo.steps.length) { el.style.display = "none"; return; }
  let idx = 0;
  const demoGoal = demo.steps[0]?.context?.goal ?? demo.goal;
  el.innerHTML = "<h2>🎬 演示关——看一遍完整的证明</h2>"
    + `<div class="goal-box"><span class="hole">?</span> : ${esc(demoGoal)}</div>`
    + `<div id="demo-steps"></div>`
    + `<div class="demo-controls">
         <button class="btn primary" id="demo-next">▶ 下一步</button>
         <button class="btn" id="demo-all">直接看完</button>
       </div><div id="demo-done"></div>`;
  const box = el.querySelector("#demo-steps") as HTMLElement;
  const nextBtn = el.querySelector("#demo-next") as HTMLButtonElement;
  const showStep = (): void => {
    if (idx >= demo.steps.length) return;
    const st = demo.steps[idx];
    const div = document.createElement("div");
    div.className = "demo-step show";
    div.innerHTML = `<div class="tactic-row"><span class="mono" style="color:var(--ok)">proof&gt;</span>
        <span class="mono">${esc(st.line)}</span></div>`
      + (st.context ? ctxHtml(st.context) : "")
      + (st.done ? `<pre class="solution-block">${esc(st.done)}</pre>` : "");
    box.appendChild(div);
    idx++;
    if (idx >= demo.steps.length) {
      nextBtn.disabled = true;
      nextBtn.textContent = "演示完毕";
      $("demo-done").innerHTML =
        `<button class="btn primary" id="to-level">到我了——进入第 1 关 ↓</button>`;
      ($("to-level") as HTMLButtonElement).onclick = () =>
        ($("level-card") as HTMLElement).scrollIntoView({ behavior: "smooth" });
    }
  };
  nextBtn.onclick = showStep;
  ($("demo-all") as HTMLButtonElement).onclick = () => {
    while (idx < demo.steps.length) showStep();
  };
}

// ---------- 关卡面板 ----------

function ctxHtml(c: Ctx): string {
  const chips = c.context.length
    ? c.context.map(([n, ty]) =>
        `<span class="chip"><b>${esc(n)}</b> : <span class="ty">${esc(ty)}</span></span>`).join("")
    : `<span class="muted">（空——还没有引入任何假设）</span>`;
  const term = esc(c.term).replace(/_/g, `<span class="cur">_</span>`);
  return `<div class="panel-label">上下文</div><div class="ctx-chips">${chips}</div>`
    + `<div class="panel-label">目标——需要写出一个类型如下的项</div>`
    + `<div class="goal-box"><span class="hole">?</span> : ${esc(c.goal)}</div>`
    + `<div class="panel-label">当前项 λ</div>`
    + `<div class="term-line">${term}</div>`
    + (c.note ? `<div class="muted">${esc(c.note)}</div>` : "");
}

function renderLevel(el: HTMLElement, lv: LevelPayload): void {
  el.innerHTML = `
    <div class="level-header">
      <h2>第 ${lv.number} 关：${esc(lv.name)}</h2>
      <span class="goal-raw mono">${esc(lv.goal)}</span>
    </div>
    <div id="level-state">${ctxHtml(lv.context)}</div>
    <div id="level-banner"></div>
    <div class="tactic-row">
      <span class="prompt">proof&gt;</span>
      <input type="text" id="tactic-in" placeholder="intro a / apply And.intro / exact ha …" autocomplete="off">
      <button class="btn primary" id="tactic-run">执行</button>
      <button class="btn" id="hint-btn">提示</button>
      <button class="btn" id="sol-btn">标准解</button>
      <button class="btn ghost" id="exit-btn">exit 离开关卡</button>
    </div>
    <div id="level-extra"></div>`;
  const input = el.querySelector("#tactic-in") as HTMLInputElement;
  const run = async (): Promise<void> => {
    const line = input.value.trim();
    if (!line) return;
    tacticHistory.push(line); historyIdx = tacticHistory.length;
    input.value = "";
    await doTactic(line);
  };
  ($("tactic-run") as HTMLButtonElement).onclick = () => void run();
  input.onkeydown = (ev: KeyboardEvent) => {
    if (ev.key === "Enter") void run();
    if (ev.key === "ArrowUp" && historyIdx > 0) input.value = tacticHistory[--historyIdx];
    if (ev.key === "ArrowDown") input.value = historyIdx < tacticHistory.length - 1
      ? tacticHistory[++historyIdx] : "";
  };
  ($("hint-btn") as HTMLButtonElement).onclick = () => void doHint();
  ($("sol-btn") as HTMLButtonElement).onclick = () => void doSolution();
  ($("exit-btn") as HTMLButtonElement).onclick = () => void doExit();
  input.focus();
}

function banner(cls: string, text: string): void {
  $("level-banner").innerHTML = text ? `<div class="banner ${cls}">${esc(text)}</div>` : "";
}

async function doTactic(line: string): Promise<void> {
  const r: TacticResp = await rpc("tactic", { line });
  const state = $("level-state");
  const extra = $("level-extra");
  if (r.kind === "error") { banner("err", r.message ?? "错误"); return; }
  banner("ok", "");
  if (r.kind === "ok" && r.context) {
    state.innerHTML = ctxHtml(r.context);
    const inp = $("tactic-in") as HTMLInputElement;
    inp.focus();
  } else if (r.kind === "completed") {
    const starStr = "★★★".slice(0, r.stars ?? 1) + "☆☆☆".slice(0, 3 - (r.stars ?? 1));
    let html = `<div class="big-stars">${starStr}</div>`
      + `<pre class="solution-block">${esc(r.output ?? "")}</pre>`
      + `<h2>标准解（你的路径可能不同，两种都正确）</h2>`
      + `<pre class="solution-block">${esc((r.solution ?? []).join("\n"))}</pre>`;
    for (const v of r.variants ?? []) html += `<div class="banner hintb">💡 变体挑战：${esc(v)}</div>`;
    if (r.next) {
      html += `<button class="btn primary" id="next-level">下一关：${esc(`第 ${r.next.number} 关 ${r.next.name}`)} →</button>`;
    } else if (r.world_done) {
      html += `<div class="banner ok">🎉 世界通关！</div>`;
      if (r.next_world) html += `<button class="btn primary" id="next-world">下一站：${esc(r.next_world)} 世界 →</button>`;
      else html += `<div class="banner ok">全部世界通关！</div>`;
    }
    extra.innerHTML = html;
    const nl = $("next-level");
    if (nl) nl.onclick = () => { if (r.next) renderLevel($("level-card"), r.next); };
    const nw = $("next-world");
    if (nw) nw.onclick = () => void enterWorld(r.next_world as string, false);
    state.innerHTML = "";
    $("level-banner").innerHTML = "";
  } else if (r.kind === "abandoned") {
    current = null;
    renderSidebar();
    renderWelcome();
  }
  refreshWorldsQuiet();
}

async function doHint(): Promise<void> {
  const r: HintResp = await rpc("hint");
  if (r.kind === "error") { banner("err", r.message ?? ""); return; }
  banner("hintb", `提示 ${r.index}/${r.total}：${r.hint ?? ""}`);
}

async function doSolution(): Promise<void> {
  const r: SolutionResp = await rpc("solution");
  if (r.kind === "error") { banner("err", r.message ?? ""); return; }
  $("level-extra").innerHTML =
    `<h2>标准解</h2><pre class="solution-block">${esc((r.solution ?? []).join("\n"))}</pre>`
    + `<div class="muted">${esc(r.note ?? "")}</div>`;
}

async function doExit(): Promise<void> {
  const r: TacticResp = await rpc("exit_level");
  if (r.kind === "abandoned") { current = null; renderSidebar(); renderWelcome(); }
}

async function refreshWorldsQuiet(): Promise<void> {
  const r: WorldsResp = await rpc("worlds");
  worlds = r.worlds;
  renderSidebar();
}

// ---------- 欢迎页 ----------

function renderWelcome(): void {
  const m = $("main");
  const inProgress = worlds.find(w => w.done > 0 && w.done < w.total)
    ?? worlds.find(w => w.done === 0);
  m.innerHTML = "<h1>nanobruijn 证明游戏</h1>"
    + `<p class="intro">在内核眼里，证明就是一台机器。选择一个世界开始——`
    + `推荐按编号顺序闯关（世界顺序即概念依赖链）。</p>`
    + (inProgress ? `<div class="banner ok">欢迎回来——续玩：${esc(inProgress.id)} 世界（第 ${inProgress.done + 1} 关起）</div>` : "")
    + `<div class="welcome-grid">${worlds.map(w =>
        `<div class="welcome-card" data-w="${esc(w.id)}">
           <span class="num">${"①②③④⑤⑥⑦⑧⑨⑩⑪"[w.index - 1] || w.index}</span>
           <b>${esc(w.id)}</b> <span class="muted">${w.done}/${w.total} 关</span>
           <div class="w-title">${esc(w.title)}</div>
           <div>${stars(Math.round((w.stars.filter(s => s > 0).reduce((a, b) => a + b, 0) / Math.max(w.total, 1))))}</div>
         </div>`).join("")}</div>`;
  for (const card of Array.from(document.getElementsByClassName("welcome-card"))) {
    (card as HTMLElement).onclick = () => enterWorld((card as HTMLElement).dataset.w!, false);
  }
}

// ---------- 控制台 ----------

async function runConsole(line: string): Promise<void> {
  const out = $("console-out");
  const trimmed = line.trim();
  if (!trimmed) return;
  let r: any;
  if (trimmed.startsWith("#reduce ")) r = await rpc("reduce", { expr: trimmed.slice(8) });
  else if (trimmed.startsWith("#print ")) r = await rpc("print_const", { name: trimmed.slice(7) });
  else if (trimmed.startsWith("#check ")) r = await rpc("check", { expr: trimmed.slice(7) });
  else if (trimmed.startsWith("#check")) r = await rpc("check", { expr: "Prop" });
  else r = await rpc("check", { expr: trimmed });
  out.textContent += `\n› ${trimmed}\n${r.output ?? r.message ?? ""}\n`;
  out.scrollTop = out.scrollHeight;
}

// ---------- 启动 ----------

async function main(): Promise<void> {
  const r: WorldsResp = await rpc("worlds");
  worlds = r.worlds;
  $("profile-badge").textContent = `档位：${r.profile}`;
  renderSidebar();
  renderWelcome();
  $("const-search").oninput = renderConsts;
  $("console-in").onkeydown = (ev: KeyboardEvent) => {
    if (ev.key === "Enter") {
      void runConsole(($("console-in") as HTMLInputElement).value);
      ($("console-in") as HTMLInputElement).value = "";
    }
  };
}

void main();
