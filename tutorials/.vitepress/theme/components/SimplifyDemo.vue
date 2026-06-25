<template>
  <div class="demo-section">
    <CustomSelect :options="selectOptions" v-model="key" />
    <div class="demo-output">{{ output }}</div>
  </div>
</template>

<script setup>
import { ref, reactive, computed, watch } from 'vue'

const levels = reactive({
  ex_real: { tag: 'Max', children: [{ tag: 'IMax', children: [{ tag: 'Zero', children: [] }, { tag: 'Succ', children: [{ tag: 'Param', children: [], name: 'u' }] }] }, { tag: 'Succ', children: [{ tag: 'Param', children: [], name: 'u' }] }] },
  ex_nested: { tag: 'Max', children: [{ tag: 'Max', children: [{ tag: 'Succ', children: [{ tag: 'Param', children: [], name: 'u' }] }, { tag: 'Succ', children: [{ tag: 'Succ', children: [{ tag: 'Param', children: [], name: 'v' }] }] }] }, { tag: 'Zero', children: [] }] },
  ex_deep: { tag: 'IMax', children: [{ tag: 'IMax', children: [{ tag: 'Succ', children: [{ tag: 'Param', children: [], name: 'u' }] }, { tag: 'Param', children: [], name: 'v' }] }, { tag: 'Zero', children: [] }] },
  ex_multi: { tag: 'Max', children: [{ tag: 'Succ', children: [{ tag: 'Succ', children: [{ tag: 'Succ', children: [{ tag: 'Zero', children: [] }] }] }] }, { tag: 'Succ', children: [{ tag: 'Zero', children: [] }] }] },
  ex_imax_prop: { tag: 'IMax', children: [{ tag: 'Zero', children: [] }, { tag: 'Succ', children: [{ tag: 'Succ', children: [{ tag: 'Zero', children: [] }] }] }] },
  ex_imax_nest: { tag: 'IMax', children: [{ tag: 'Succ', children: [{ tag: 'Zero', children: [] }] }, { tag: 'IMax', children: [{ tag: 'Zero', children: [] }, { tag: 'Succ', children: [{ tag: 'Zero', children: [] }] }] }] },
  ex_quad: { tag: 'Max', children: [{ tag: 'Max', children: [{ tag: 'Zero', children: [] }, { tag: 'IMax', children: [{ tag: 'Succ', children: [{ tag: 'Zero', children: [] }] }, { tag: 'Zero', children: [] }] }] }, { tag: 'Succ', children: [{ tag: 'Succ', children: [{ tag: 'Param', children: [], name: 'w' }] }] }] },
})

const key = ref('ex_real')
const output = ref('')

function clone(l) { return l ? { tag: l.tag, children: l.children.map(clone), name: l.name } : null }
function isZero(l) { return l && l.tag === 'Zero' }
function isOne(l) { return l && l.tag === 'Succ' && l.children[0].tag === 'Zero' }
function combine(l, r) {
  if (!l || !r) return clone(l || r)
  if (l.tag === 'Zero') return clone(r)
  if (r.tag === 'Zero') return clone(l)
  if (l === r || (l.tag === 'Param' && r.tag === 'Param' && l.name === r.name)) return clone(l)
  if (l.tag === 'Succ' && r.tag === 'Succ') return { tag: 'Succ', children: [combine(l.children[0], r.children[0])] }
  return { tag: 'Max', children: [clone(l), clone(r)] }
}
function simplify(l) {
  if (!l) return null
  const t = l.tag
  if (t === 'Zero' || t === 'Param') return clone(l)
  if (t === 'Succ') return { tag: 'Succ', children: [simplify(l.children[0])] }
  if (t === 'Max') return combine(simplify(l.children[0]), simplify(l.children[1]))
  if (t === 'IMax') {
    const a = simplify(l.children[0]), b = simplify(l.children[1])
    if (isZero(a) || isOne(a)) return clone(b)
    if (b.tag === 'Zero') return clone(b)
    if (b.tag === 'Succ') return combine(a, b)
    return { tag: 'IMax', children: [a, b] }
  }
  return clone(l)
}
function fmt(l) {
  if (!l) return '?'
  if (l.tag === 'Zero') return '0'
  if (l.tag === 'Param') return l.name || '?'
  if (l.tag === 'Succ') { const i = fmt(l.children[0]); return i === '0' ? '1' : i === '1' ? '2' : 'Succ(' + i + ')' }
  if (l.tag === 'Max') return 'Max(' + fmt(l.children[0]) + ', ' + fmt(l.children[1]) + ')'
  if (l.tag === 'IMax') return 'IMax(' + fmt(l.children[0]) + ', ' + fmt(l.children[1]) + ')'
  return '?'
}
const selectOptions = computed(() =>
  Object.keys(levels).map(k => ({ value: k, label: fmt(levels[k]) }))
)

function run() {
  const e = levels[key.value]
  if (!e) return
  const r = simplify(e)
  output.value = '输入: ' + fmt(e) + '\n输出: ' + fmt(r)
}
watch(key, run)
setTimeout(run, 0)
</script>

<style scoped>
.demo-section { background: var(--vp-c-bg-soft); border: 1px solid var(--vp-c-divider); border-radius: 8px; padding: 1rem; margin: 0.5rem 0; }
.demo-output { background: var(--vp-c-bg); border: 1px solid var(--vp-c-divider); border-radius: 4px; padding: 0.5rem 0.8rem; margin-top: 0.5rem; font-size: 0.85rem; white-space: pre-wrap; min-height: 3rem; font-family: 'SF Mono', monospace; }
</style>
