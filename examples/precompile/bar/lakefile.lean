import Lake
open Lake DSL

package bar {
  precompileModules := false
}

require foo from "../foo"

@[default_target]
lean_lib Bar
