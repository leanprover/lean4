import Lake
import Lean.Meta
open System Lake DSL

package test

require hello from git "../hello"

@[default_target]
lean_exe test where
  root := `Main
