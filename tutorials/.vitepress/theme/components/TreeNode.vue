<template>
  <div class="tree-node-wrapper">
    <div class="tree-node" :style="{ paddingLeft: depth * 20 + 'px' }" @click="toggleNode(node)">
      <span v-if="node.children && node.children.length" class="arrow">{{ node.open ? '▾' : '▸' }}</span>
      <span v-else class="arrow-placeholder"></span>
      <span :class="['node-label', { anon: node.anon }]">
        {{ node.anon ? 'Anon' : node.name }}
      </span>
    </div>
    <div v-if="node.open && node.children && node.children.length" class="tree-children">
      <TreeNode v-for="(child, i) in node.children" :key="i" :node="child" :depth="depth + 1" />
    </div>
  </div>
</template>

<script setup>
import { inject } from 'vue'
defineProps({ node: Object, depth: { type: Number, default: 0 } })
const toggleNode = inject('toggleNode')
</script>

<style scoped>
.tree-node-wrapper { }
.tree-node {
  display: flex;
  align-items: center;
  padding: 3px 0;
  cursor: pointer;
  border-radius: 4px;
  transition: background 0.15s;
}
.tree-node:hover { background: var(--vp-c-bg-soft); }
.arrow { display: inline-block; width: 16px; color: var(--vp-c-text-3); user-select: none; }
.arrow-placeholder { display: inline-block; width: 16px; }
.node-label {
  display: inline-block;
  padding: 1px 10px;
  border: 1px solid var(--vp-c-brand-1);
  border-radius: 4px;
  background: var(--vp-c-bg-soft);
  transition: background 0.15s;
}
.node-label:hover { background: var(--vp-c-brand-soft); }
.node-label.anon { border-color: var(--vp-c-text-3); color: var(--vp-c-text-3); font-size: 0.75rem; }
</style>
