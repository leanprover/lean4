import Lake
open Lake DSL

package bar {
  precompileModules := false
}

require foo from "../foo"

@[defaultTarget]
lean_lib Bar
