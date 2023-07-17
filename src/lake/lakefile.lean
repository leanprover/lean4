import Lake.DSL
open System Lake DSL

package lake

lean_lib Lake

@[default_target]
lean_exe lake where
  root := `Lake.Main
  supportInterpreter := true
