import { defineConfig } from 'vitepress'

export default defineConfig({
  lang: 'zh-CN',
  title: 'py_nanobruijn',
  description: 'Lean 4 类型检查器核心知识教程',
  base: '/',

  themeConfig: {
    nav: [
      { text: '首页', link: '/' },
    ],

    sidebar: [
      { text: '📖 导学', link: '/' },
      {
        text: '第一章 数据结构基础',
        collapsed: false,
        items: [
          { text: 'Name — 名字系统', link: '/name' },
          { text: 'Level — 宇宙层级', link: '/level' },
          { text: 'Expr — 表达式 DAG', link: '/expr' },
        ],
      },
      {
        text: '第二章 类型检查算法',
        collapsed: false,
        items: [
          { text: 'WHNF — 弱头范式', link: '/whnf' },
          { text: 'Infer — 类型推断', link: '/infer' },
          { text: 'DefEq — 定义性等价', link: '/defeq' },
        ],
      },
    ],

    socialLinks: [
      { icon: 'github', link: 'https://github.com/leanprover-community/nanobruijn' },
    ],

    footer: {
      message: '基于 py_nanobruijn 源码',
      copyright: 'Apache-2.0 License',
    },
  },
})
