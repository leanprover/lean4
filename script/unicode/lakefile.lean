import Lake
open Lake DSL

package "Unicode" where
  -- add package configuration options here

lean_lib «Unicode» where
  -- add library configuration options here

@[default_target]
lean_exe "generate_tables" where
  root := `Generation

lean_exe "verify_tables" where
  root := `Verification
