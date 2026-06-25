<template>
  <div class="cs-wrapper" @blur="open = false" tabindex="0">
    <div class="cs-trigger" @click="toggle" :class="{ focused: open }">
      <span class="cs-value">{{ display }}</span>
      <span class="cs-arrow">▾</span>
    </div>
    <div v-if="open" class="cs-menu">
      <div
        v-for="(opt, i) in options"
        :key="i"
        class="cs-option"
        :class="{ selected: opt.value === modelValue }"
        @mousedown.prevent="select(opt.value)"
      >{{ opt.label }}</div>
    </div>
  </div>
</template>

<script setup>
import { ref, computed } from 'vue'

const props = defineProps({ options: Array, modelValue: String })
const emit = defineEmits(['update:modelValue'])
const open = ref(false)

const display = computed(() => {
  const opt = props.options.find(o => o.value === props.modelValue)
  return opt ? opt.label : ''
})

function toggle() { open.value = !open.value }
function select(val) {
  emit('update:modelValue', val)
  open.value = false
}

// Close on click outside
function onClick(e) {
  if (!e.target.closest('.cs-wrapper')) open.value = false
}
if (typeof window !== 'undefined') document.addEventListener('click', onClick)
</script>

<style scoped>
.cs-wrapper {
  position: relative;
  font-family: 'SF Mono', 'Cascadia Code', monospace;
  font-size: 0.85rem;
  outline: none;
  max-width: 400px;
}
.cs-trigger {
  display: flex;
  align-items: center;
  justify-content: space-between;
  padding: 6px 10px;
  background: var(--vp-c-bg);
  border: 1px solid var(--vp-c-divider);
  border-radius: 6px;
  cursor: pointer;
  transition: border-color 0.2s;
  user-select: none;
}
.cs-trigger:hover, .cs-trigger.focused { border-color: var(--vp-c-brand-1); }
.cs-value { color: var(--vp-c-text-1); }
.cs-arrow { color: var(--vp-c-text-3); font-size: 0.7rem; margin-left: 8px; transition: transform 0.2s; }
.cs-trigger.focused .cs-arrow { transform: rotate(180deg); }
.cs-menu {
  position: absolute;
  top: 100%;
  left: 0;
  right: 0;
  z-index: 100;
  margin-top: 2px;
  background: var(--vp-c-bg);
  border: 1px solid var(--vp-c-divider);
  border-radius: 6px;
  box-shadow: 0 4px 12px rgba(0,0,0,0.15);
  overflow: hidden;
}
.cs-option {
  padding: 6px 10px;
  cursor: pointer;
  transition: background 0.1s;
  color: var(--vp-c-text-1);
}
.cs-option:hover { background: var(--vp-c-brand-soft); }
.cs-option.selected { background: var(--vp-c-brand-soft); color: var(--vp-c-brand-1); font-weight: 600; }
</style>
