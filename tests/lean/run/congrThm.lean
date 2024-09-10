import Lean

open Lean
open Lean.Meta

def test (f : Expr) : MetaM Unit := do
  let some thm  ← mkCongrSimp? f | unreachable!
  check thm.type
  check thm.proof
  assert! (← isDefEq thm.type (← inferType thm.proof))
  IO.println (← Meta.ppExpr thm.type)

/--
info: ∀ (p p_1 : Prop), p = p_1 → ∀ {h : Decidable p} [h_1 : Decidable p_1], decide p = decide p_1
-/
#guard_msgs in
#eval test (mkConst ``decide)

/--
info: ∀ {α : Type} (a a_1 : Array α) (e_a : a = a_1) (i i_1 : USize) (e_i : i = i_1) (h : i.toNat < a.size),
  a.uget i h = a_1.uget i_1 ⋯
-/
#guard_msgs in
#eval test (mkConst ``Array.uget [levelZero])
