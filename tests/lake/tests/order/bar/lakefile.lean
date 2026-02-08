import Lake
open Lake DSL

package bar where
  moreLeanArgs := #["-DmaxHeartbeats=888000"]

require baz from ".." / "baz"
require leaf from ".." / "leaf" with NameMap.empty.insert `val "888000"

lean_lib X
lean_exe Y
