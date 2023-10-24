import Lake
open Lake DSL

package order
require foo from "foo"
require bar from "bar"

lean_lib A.B where
  moreLeanArgs := #["-DmaxHeartbeats=333000"]

lean_lib A.B.C where
  moreLeanArgs := #["-DmaxHeartbeats=444000"]

lean_lib A where
  moreLeanArgs := #["-DmaxHeartbeats=222000"]
