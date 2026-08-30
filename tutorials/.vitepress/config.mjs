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
        text: '🎯 教学剧本（#prove Playbook）',
        collapsed: false,
        items: [
          { text: '第一公里 · 三节路径', link: '/prove-playbook' },
        ],
      },
      {
        text: '第一部分 数据结构基础',
        collapsed: false,
        items: [
          { text: '第一讲 Name — 名字系统', link: '/name' },
          { text: '第二讲 Level — 宇宙层级', link: '/level' },
          { text: '第三讲 Expr — 表达式 DAG', link: '/expr' },
        ],
      },
      {
        text: '第二部分 类型检查算法',
        collapsed: false,
        items: [
          { text: '第四讲 WHNF — 弱头范式', link: '/whnf' },
          { text: '第五讲 Infer — 类型推断', link: '/infer' },
          { text: '第六讲 DefEq — 定义性等价', link: '/defeq' },
          { text: '第七讲 TcCache — 缓存系统', link: '/cache' },
        ],
      },
      {
        text: '第三部分 前端与顶层编排',
        collapsed: false,
        items: [
          { text: '第八讲 Parser — 导出文件解析', link: '/parser' },
          { text: '第九讲 Env — 环境系统', link: '/env' },
          { text: '第十讲 Inductive — 归纳类型检查', link: '/inductive' },
          { text: '第十一讲 check_decl — 声明检查', link: '/check_decl' },
        ],
      },
      {
        text: '第四部分 运行与测试',
        collapsed: false,
        items: [
          { text: '第十二讲 运行与测试', link: '/running' },
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
