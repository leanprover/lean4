import Lean
open Lean
open Lean.Meta

def test : MetaM Unit := do
  let x ← mkFreshExprMVar (mkConst ``Nat)
  let y ← mkFreshExprMVar (mkConst ``Nat)
  let add := mkConst ``Nat.add
  let e := mkApp3 add x (mkNatLit 1) y
  IO.println (e.abstract #[x, y])
  assert! e.abstract #[x, y] == mkApp3 add (mkBVar 1) (mkNatLit 1) (mkBVar 0)

/-- info: Nat.add #1 (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)) #0 -/
#guard_msgs in
#eval test
