import Lake
open Lake DSL

package foo where
  moreLeanArgs := #["-DmaxHeartbeats=777000"]

require leaf from ".." / "leaf" with NameMap.empty.insert `val "777000"

lean_lib X
lean_exe Y
