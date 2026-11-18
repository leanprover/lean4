module
import Lean.Util.FoldConsts

open Lean Meta

/-- info: #[`S, `S.mk] -/
#guard_msgs in
#eval Expr.getUsedConstants (.proj `S 0 (mkConst `S.mk))
