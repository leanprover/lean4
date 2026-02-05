import Lean

/-- info: (a + 1).add a -/
#guard_msgs in
open Lean Meta Sym in
run_meta SymM.run do
  let s₁ ← share <| mkLambda `x .default Nat.mkType (mkApp (mkConst ``Nat.add) (mkNatAdd (mkBVar 0) (mkNatLit 1)))
  let s₂ ← share <| mkConst `a
  let e  ← share <| mkApp2 (mkBVar 1) (mkBVar 0) (mkBVar 0)
  logInfo <| (← instantiateRevBetaS e #[s₁, s₂])
