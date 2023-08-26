import Lake
open Lake DSL

script nop :=
  return 0

def test := get_config? test |>.getD "Test"

package lean4 where
  buildDir := defaultBuildDir / test
  srcDir := ".." / ".." / "src"

@[default_target]
lean_lib Init

@[default_target]
lean_lib Lean

@[default_target]
lean_lib Lake where
  srcDir := "lake"

@[default_target]
lean_exe lake where
  srcDir := "lake"
  root := `Lake.Main
  supportInterpreter := true

