import Lake
open Lake DSL

package frontend

@[default_target]
lean_lib Frontend

@[default_target]
lean_exe frontend {
  root := `Main
  supportInterpreter := true
}
