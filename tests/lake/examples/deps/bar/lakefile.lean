import Lake
open System Lake DSL

package bar

/-- Require statements can have doc comments. -/
require foo from ".."/"foo"

lean_lib Bar

@[default_target]
lean_exe bar where
  root := `Main
