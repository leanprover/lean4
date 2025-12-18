import Lake
open Lake DSL

package frontend

@[default_target]
lean_lib Frontend

lean_exe frontend_with_import2 {
  root := `Frontend.Main_with_Import2
  supportInterpreter := true
}

lean_exe frontend {
  root := `Frontend.Main
  supportInterpreter := true
}
