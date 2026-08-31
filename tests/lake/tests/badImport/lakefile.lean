import Lake
open Lake DSL

package test

lean_lib Lib where
  globs := #[`Lib.+]

lean_lib Etc

lean_exe X
lean_exe X1
