import Lake
open System Lake DSL

package lake where
  srcDir := ".." / ".."

lean_lib Lake

@[defaultTarget]
lean_exe lake where
  root := `Lake.Main
  supportInterpreter := true
