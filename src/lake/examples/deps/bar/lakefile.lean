import Lake
open System Lake DSL

package bar

require foo from ".."/"foo"

lean_lib Bar

@[default_target]
lean_exe bar where
  root := `Main
