import Std.Tactic.Do

/-! Tests that `mvcgen'` is usable as a step inside `sym => …` blocks. -/

open Std.Do

set_option mvcgen.warning false
set_option warn.sorry false

/-! ## Trivial postcondition: `mvcgen'` closes the goal -/

axiom G : StateM Nat Unit
axiom H : StateM Nat Unit

noncomputable def F : StateM Nat Unit := do
  G
  H

@[spec]
axiom G_spec : ⦃⌜True⌝⦄ G ⦃⇓ _ n => ⌜n = n⌝⦄

@[spec]
axiom H_spec : ⦃⌜True⌝⦄ H ⦃⇓ _ n => ⌜n = n⌝⦄

example : ⦃⌜True⌝⦄ F ⦃⇓ _ n => ⌜n = n⌝⦄ := by
  sym =>
    mvcgen' [F]

/-! ## Pre-tactic dispatches the leftover VC -/

axiom G2 : StateM Nat Unit
axiom H2 : StateM Nat Unit

noncomputable def F2 : StateM Nat Unit := do
  G2
  H2

axiom P : Nat → Prop

@[spec]
axiom G2_spec : ⦃⌜True⌝⦄ G2 ⦃⇓ _ n => ⌜P n⌝⦄

@[spec]
axiom H2_spec : ⦃fun n => ⌜P n⌝⦄ H2 ⦃⇓ _ n => ⌜True⌝⦄

example : ⦃⌜True⌝⦄ F2 ⦃⇓ _ n => ⌜True⌝⦄ := by
  sym =>
    mvcgen' [F2] <;> finish

/-! ## VC leftover; closed by a subsequent grind step -/

axiom G3 : StateM Nat Unit
axiom H3 : StateM Nat Unit

noncomputable def F3 : StateM Nat Unit := do
  G3
  H3

axiom Q : Nat → Prop
axiom hPQ : ∀ n, P n → Q n

@[spec]
axiom G3_spec : ⦃⌜True⌝⦄ G3 ⦃⇓ _ n => ⌜P n⌝⦄

@[spec]
axiom H3_spec : ⦃fun n => ⌜Q n⌝⦄ H3 ⦃⇓ _ n => ⌜True⌝⦄

example : ⦃⌜True⌝⦄ F3 ⦃⇓ _ n => ⌜True⌝⦄ := by
  sym =>
    mvcgen' [F3]
    finish [hPQ]

-- `sym [hPQ]` propagates to the new VC `Grind.Goal`s; no need to re-pass it.
example : ⦃⌜True⌝⦄ F3 ⦃⇓ _ n => ⌜True⌝⦄ := by
  sym [hPQ] =>
    mvcgen' [F3]
    finish

/-! ## VC references an fvar introduced by `mvcgen'` -/

axiom G4 : StateM Nat Nat
axiom Q4 : Nat → Prop
axiom hPQ4 : ∀ n, P n → Q4 n

@[spec]
axiom G4_spec : ⦃⌜True⌝⦄ G4 ⦃⇓ x _ => ⌜P x⌝⦄

noncomputable def F4 : StateM Nat Nat := do
  let x ← G4
  pure x

-- `mvcgen'` introduces `x` and a hypothesis `P x` into the VC's local context.
-- The subsequent `finish [hPQ4]` must see `P x` in the E-graph to derive `Q4 x`.
example : ⦃⌜True⌝⦄ F4 ⦃⇓ r _ => ⌜Q4 r⌝⦄ := by
  sym =>
    mvcgen' [F4]
    finish [hPQ4]

/-! ## Inline invariants (bullet form) inside `sym =>` -/

example :
    ⦃⌜True⌝⦄
    (do
      let mut x := 0
      for i in [1:5] do
        x := x + i
      pure x : Id Nat)
    ⦃⇓r => ⌜r < 30⌝⦄ := by
  sym =>
    mvcgen' invariants
      · ⇓(xs, r) => ⌜r + xs.suffix.length * 5 ≤ 25⌝
    <;> finish

/-! ## `invariants?` (suggest mode) works inside `sym =>` -/

def mySum (l : List Nat) : Nat := Id.run do
  let mut acc := 0
  for x in l do
    acc := acc + x
  return acc

/--
info: Try this:
  [apply] invariants
  · ⇓⟨xs, letMuts⟩ => ⌜xs.prefix = [] ∧ letMuts = 0 ∨ xs.suffix = [] ∧ letMuts = l.sum⌝
-/
#guard_msgs (info) in
theorem mySum_suggest (l : List Nat) : mySum l = l.sum := by
  generalize h : mySum l = r
  apply Id.of_wp_run_eq h
  sym =>
    mvcgen' [mySum] invariants?
    all_goals tactic => admit
