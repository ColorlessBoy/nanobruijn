import DefaultTheme from 'vitepress/theme'
import NameTree from './components/NameTree.vue'
import SimplifyDemo from './components/SimplifyDemo.vue'
import LeqDemo from './components/LeqDemo.vue'
import CustomSelect from './components/CustomSelect.vue'

export default {
  extends: DefaultTheme,
  enhanceApp({ app }) {
    app.component('NameTree', NameTree)
    app.component('SimplifyDemo', SimplifyDemo)
    app.component('LeqDemo', LeqDemo)
    app.component('CustomSelect', CustomSelect)
  },
}
