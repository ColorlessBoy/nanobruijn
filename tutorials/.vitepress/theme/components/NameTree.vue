<template>
  <div class="name-tree-demo">
    <TreeNode v-for="(child, i) in tree.children" :key="i" :node="child" :depth="0" />
  </div>
</template>

<script setup>
import { reactive, provide } from 'vue'
import TreeNode from './TreeNode.vue'

const tree = reactive({
  children: [
    { name: 'Nat', open: false, children: [
      { name: 'Nat.zero', open: false, children: [] },
      { name: 'Nat.succ', open: false, children: [] },
      { name: 'Nat.add', open: false, children: [] },
      { name: 'Nat.mul', open: false, children: [] },
    ]},
    { name: 'List', open: false, children: [
      { name: 'List.map', open: false, children: [] },
      { name: 'List.foldl', open: false, children: [] },
    ]},
    { name: 'Eq', open: false, children: [
      { name: 'Eq.refl', open: false, children: [] },
      { name: 'Eq.symm', open: false, children: [] },
    ]},
  ],
})

function toggleNode(node) {
  node.open = !node.open
}

provide('toggleNode', toggleNode)
</script>

<style scoped>
.name-tree-demo {
  padding: 0.5rem 0;
  font-family: 'SF Mono', 'Cascadia Code', monospace;
  font-size: 0.85rem;
}
</style>
