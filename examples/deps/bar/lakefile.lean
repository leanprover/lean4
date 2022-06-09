import Lake
open System Lake DSL

package bar

require foo from ".."/"foo"

lean_lib Bar

@[defaultTarget]
lean_exe bar where
  root := `Main
