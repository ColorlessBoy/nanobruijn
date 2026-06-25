<template>
  <div class="demo-section">
    <div class="leq-pair">
      <div class="leq-side">
        <div class="leq-label">左侧 (lv)</div>
        <CustomSelect :options="selectOptions" v-model="lv" />
      </div>
      <div class="leq-vs">≤</div>
      <div class="leq-side">
        <div class="leq-label">右侧 (r)</div>
        <CustomSelect :options="selectOptions" v-model="rv" />
      </div>
    </div>
    <div class="demo-output" :class="result !== null ? (result ? 'ok' : 'err') : ''">{{ output }}</div>
    <div class="leq-trace">{{ trace }}</div>
  </div>
</template>

<script setup>
import { ref, reactive, computed, watch } from 'vue'

const levels = reactive({
  zero: { tag: 'Zero', children: [] },
  succ_zero: { tag: 'Succ', children: [{ tag: 'Zero', children: [] }] },
  succ_succ_zero: { tag: 'Succ', children: [{ tag: 'Succ', children: [{ tag: 'Zero', children: [] }] }] },
  param_u: { tag: 'Param', children: [], name: 'u' },
  max_nest: { tag: 'Max', children: [{ tag: 'Succ', children: [{ tag: 'Zero', children: [] }] }, { tag: 'Succ', children: [{ tag: 'Succ', children: [{ tag: 'Zero', children: [] }] }] }] },
})

const lv = ref('succ_zero')
const rv = ref('succ_succ_zero')
const result = ref(null)
const output = ref('')
const trace = ref('')

const selectOptions = computed(() =>
  Object.keys(levels).map(k => ({ value: k, label: fmt(levels[k]) }))
)

function fmt(l) {
  if (!l) return '?'
  if (l.tag === 'Zero') return '0'
  if (l.tag === 'Param') return l.name || '?'
  if (l.tag === 'Succ') { const i = fmt(l.children[0]); return i === '0' ? '1' : 'Succ(' + i + ')' }
  if (l.tag === 'Max') return 'Max(' + fmt(l.children[0]) + ', ' + fmt(l.children[1]) + ')'
  return '?'
}

function run() {
  const a = levels[lv.value], b = levels[rv.value]
  if (!a || !b) return
  const t = []
  const r = leq(a, b, 0, t)
  result.value = r
  output.value = 'leq(' + fmt(a) + ', ' + fmt(b) + ') = ' + (r ? 'true ✅' : 'false ❌')
  trace.value = t.join('\n')
}

function leq(l, r, diff, t) {
  if (!l || !r) return false
  t.push('leq(' + fmt(l) + ', ' + fmt(r) + ', diff=' + diff + ')')
  const lt = l.tag, rt = r.tag
  if (lt === 'Zero' && diff >= 0) { t.push('  → ✅'); return true }
  if (rt === 'Zero' && diff < 0) { t.push('  → ❌'); return false }
  if (lt === 'Param' && rt === 'Param' && l.name === r.name && diff >= 0) { t.push('  → ✅'); return true }
  if (lt === 'Param' && rt === 'Zero') { t.push('  → ❌'); return false }
  if (lt === 'Zero' && rt === 'Param') { t.push('  → ' + (diff >= 0 ? '✅' : '❌')); return diff >= 0 }
  if (lt === 'Succ') { t.push('  → peel L'); return leq(l.children[0], r, diff - 1, t) }
  if (rt === 'Succ') { t.push('  → peel R'); return leq(l, r.children[0], diff + 1, t) }
  if (lt === 'Max') { t.push('  → split L'); return leq(l.children[0], r, diff, t) && leq(l.children[1], r, diff, t) }
  if (rt === 'Max' && (lt === 'Param' || lt === 'Zero')) { t.push('  → split R'); return leq(l, r.children[0], diff, t) || leq(l, r.children[1], diff, t) }
  t.push('  → unhandled')
  return false
}
watch([lv, rv], run)
setTimeout(run, 0)
</script>

<style scoped>
.demo-section { background: var(--vp-c-bg-soft); border: 1px solid var(--vp-c-divider); border-radius: 8px; padding: 1rem; margin: 0.5rem 0; }
.leq-pair { display: flex; align-items: center; gap: 1rem; }
.leq-side { flex: 1; min-width: 0; }
.leq-label { font-size: 0.8rem; color: var(--vp-c-text-2); margin-bottom: 0.2rem; font-family: 'SF Mono', 'Cascadia Code', monospace; }
.leq-vs { font-size: 1.5rem; font-weight: 700; color: var(--vp-c-brand-1); font-family: 'SF Mono', monospace; flex-shrink: 0; }
.demo-output { background: var(--vp-c-bg); border: 1px solid var(--vp-c-divider); border-radius: 4px; padding: 0.5rem 0.8rem; margin-top: 0.5rem; font-size: 0.85rem; white-space: pre-wrap; min-height: 3rem; font-family: 'SF Mono', monospace; }
.demo-output.ok { border-left: 3px solid var(--vp-c-green-1); }
.demo-output.err { border-left: 3px solid var(--vp-c-red-1); }
.leq-trace { font-size: 0.8rem; color: var(--vp-c-text-2); white-space: pre-wrap; margin-top: 0.5rem; max-height: 200px; overflow-y: auto; font-family: 'SF Mono', monospace; }
</style>
