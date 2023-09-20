import Lake
open Lake DSL

package foo

lean_lib X where
  moreLeanArgs := #["-DmaxHeartbeats=111000"]
