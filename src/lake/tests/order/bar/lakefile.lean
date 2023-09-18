import Lake
open Lake DSL

package bar

lean_lib X where
  moreLeanArgs := #["-DmaxHeartbeats=555000"]
