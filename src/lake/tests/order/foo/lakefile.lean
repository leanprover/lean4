import Lake
open Lake DSL

package foo where
  moreLeanArgs := #["-DmaxHeartbeats=555000"]

lean_lib X
lean_exe Y
