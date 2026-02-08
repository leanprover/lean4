import Lake
open Lake DSL

def val := get_config? val |>.getD "0"

package leaf where
  moreLeanArgs := #[s!"-DmaxHeartbeats={val}"]

lean_lib Z
