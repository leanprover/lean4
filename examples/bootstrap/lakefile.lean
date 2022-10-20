import Lake
open System Lake DSL

package lake where
  srcDir := ".." / ".."

lean_lib Lake

@[default_target]
lean_exe lake where
  root := `Lake.Main
  supportInterpreter := true
