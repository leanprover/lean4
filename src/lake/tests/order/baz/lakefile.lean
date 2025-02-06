import Lake
open Lake DSL

package baz where
  moreLeanArgs := #["-DmaxHeartbeats=999000"]

lean_lib X
