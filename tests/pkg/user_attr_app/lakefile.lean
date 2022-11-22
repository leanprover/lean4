import Lake
open System Lake DSL

package user_attr

lean_lib UserAttr

@[default_target]
lean_exe user_attr where
  root := `Main
  supportInterpreter := true
