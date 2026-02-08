import Lean

open Lean Meta

def g : Nat → String := fun _ => ""

/--
info: String
[A]
-/
#guard_msgs in
run_meta do
  withLetDecl `A (mkSort 1) (← mkArrow (mkConst ``Nat) (mkConst ``String)) fun A => do
  withLetDecl `g A (mkConst ``g) fun g => do
    let e := mkApp g (mkNatLit 0)
    withTrackingZetaDelta do
      IO.println (← ppExpr (← inferType e))
      IO.println s!"{← (← getZetaDeltaFVarIds).toList.mapM fun x => ppExpr (mkFVar x)}"

/--
info: String
String
[A]
-/
#guard_msgs in
run_meta do
  withLetDecl `A (mkSort 1) (← mkArrow (mkConst ``Nat) (mkConst ``String)) fun A => do
  withLetDecl `g A (mkConst ``g) fun g => do
    let e := mkApp g (mkNatLit 0)
    IO.println (← ppExpr (← inferType e))
    withTrackingZetaDelta do
      IO.println (← ppExpr (← inferType e))
      IO.println s!"{← (← getZetaDeltaFVarIds).toList.mapM fun x => ppExpr (mkFVar x)}"
