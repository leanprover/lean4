import Lake
open Lake DSL

package bar where
  moreLeanArgs := #["-DmaxHeartbeats=555000"]

lean_lib X
lean_exe Y
