import Lean
opaque g (p : Prop) [Decidable p] (a : Nat) (h : a > 0) : Nat

open Lean Meta
def test (flag : Bool) : MetaM Unit := do
  let some congrThm ← mkCongrSimp? (mkConst ``g) (subsingletonInstImplicitRhs := flag) | throwError "failed to generate theorem"
  IO.println (← ppExpr congrThm.type)

#eval test false
#eval test true
