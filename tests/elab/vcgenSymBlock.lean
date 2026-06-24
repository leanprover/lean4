import Std.Internal.Do
import Std.Tactic.Do

/-! Tests that `vcgen` is usable as a step inside `sym => …` blocks. -/

open Std.Internal.Do Lean.Order

set_option mvcgen.warning false
set_option warn.sorry false

/-! ## Trivial postcondition: `vcgen` closes the goal -/

axiom G : StateM Nat Unit
axiom H : StateM Nat Unit

noncomputable def F : StateM Nat Unit := do
  G
  H

@[spec]
axiom G_spec : ⦃ (fun (_ : Nat) => True) ⦄ G ⦃ fun _ n => n = n ⦄

@[spec]
axiom H_spec : ⦃ (fun (_ : Nat) => True) ⦄ H ⦃ fun _ n => n = n ⦄

example : ⦃ (fun (_ : Nat) => True) ⦄ F ⦃ fun _ n => n = n ⦄ := by
  sym =>
    vcgen [F]

/-! ## Pre-tactic dispatches the leftover VC -/

axiom G2 : StateM Nat Unit
axiom H2 : StateM Nat Unit

noncomputable def F2 : StateM Nat Unit := do
  G2
  H2

axiom P : Nat → Prop

@[spec]
axiom G2_spec : ⦃ (fun (_ : Nat) => True) ⦄ G2 ⦃ fun _ n => P n ⦄

@[spec]
axiom H2_spec : ⦃ (fun n => P n) ⦄ H2 ⦃ fun _ _ => True ⦄

example : ⦃ (fun (_ : Nat) => True) ⦄ F2 ⦃ fun _ _ => True ⦄ := by
  sym =>
    vcgen [F2] <;> finish

/-! ## VC leftover; closed by a subsequent grind step -/

axiom G3 : StateM Nat Unit
axiom H3 : StateM Nat Unit

noncomputable def F3 : StateM Nat Unit := do
  G3
  H3

axiom Q : Nat → Prop
axiom hPQ : ∀ n, P n → Q n

@[spec]
axiom G3_spec : ⦃ (fun (_ : Nat) => True) ⦄ G3 ⦃ fun _ n => P n ⦄

@[spec]
axiom H3_spec : ⦃ (fun n => Q n) ⦄ H3 ⦃ fun _ _ => True ⦄

example : ⦃ (fun (_ : Nat) => True) ⦄ F3 ⦃ fun _ _ => True ⦄ := by
  sym =>
    vcgen [F3]
    finish [hPQ]

-- `sym [hPQ]` propagates to the new VC `Grind.Goal`s; no need to re-pass it.
example : ⦃ (fun (_ : Nat) => True) ⦄ F3 ⦃ fun _ _ => True ⦄ := by
  sym [hPQ] =>
    vcgen [F3]
    finish

/-! ## VC references an fvar introduced by `vcgen` -/

axiom G4 : StateM Nat Nat
axiom Q4 : Nat → Prop
axiom hPQ4 : ∀ n, P n → Q4 n

@[spec]
axiom G4_spec : ⦃ (fun (_ : Nat) => True) ⦄ G4 ⦃ fun x _ => P x ⦄

noncomputable def F4 : StateM Nat Nat := do
  let x ← G4
  pure x

-- `vcgen` introduces `x` and a hypothesis `P x` into the VC's local context.
-- The subsequent `finish [hPQ4]` must see `P x` in the E-graph to derive `Q4 x`.
example : ⦃ (fun (_ : Nat) => True) ⦄ F4 ⦃ fun r _ => Q4 r ⦄ := by
  sym =>
    vcgen [F4]
    finish [hPQ4]

/-! ## Inline invariants (bullet form) inside `sym =>` -/

example :
    ⦃ (True : Prop) ⦄
    (do
      let mut x := 0
      for i in [1:5] do
        x := x + i
      pure x : Id Nat)
    ⦃ fun r => r < 30 ⦄ := by
  sym =>
    vcgen invariants
      · fun xs r => r + xs.suffix.length * 5 ≤ 25
    <;> finish

/-! ## `invariants?` (suggest mode) inside `sym =>` -/

def mySum (l : List Nat) : Nat := Id.run do
  let mut acc := 0
  for x in l do
    acc := acc + x
  return acc

/--
info: There were no suggestions for missing invariants.
-/
#guard_msgs (info) in
theorem mySum_suggest (l : List Nat) : mySum l = l.sum := by
  generalize h : mySum l = r
  apply Std.Internal.Do.Id.of_wp_run_eq h
  sym =>
    vcgen [mySum] invariants?
    all_goals tactic => admit
