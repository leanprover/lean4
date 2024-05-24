import Lake
open Lake DSL

package «dep» where
  -- add package configuration options here

lean_lib «Dep» where
  -- add library configuration options here

@[default_target]
lean_exe «dep» where
  root := `Main
