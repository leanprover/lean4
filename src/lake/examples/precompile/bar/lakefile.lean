import Lake
open Lake DSL

package bar where
  precompileModules := false

require foo from "../foo"

@[default_target]
lean_lib Bar
