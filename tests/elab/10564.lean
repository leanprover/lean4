import Std.Tactic.Do
open Std.Do

set_option mvcgen.warning false

structure Supply where
  counter : Nat
  limit : Nat
  property : counter ≤ limit

def mkFreshN2 (n : Nat) : ExceptT Char (EStateM String Supply) (List Nat) := do
  let mut acc := #[]
  for _ in [:n] do
    let supply ← get
    if h : supply.counter = supply.limit then
      throwThe String s!"Supply exhausted: {supply.counter} = {supply.limit}"
    else
      let n := supply.counter
      have := supply.property
      set {supply with counter := n + 1, property := by omega}
      acc := acc.push n
  pure acc.toList

theorem mkFreshN2_spec2 (n : Nat) :
    ⦃⌜True⌝⦄
    mkFreshN2 n
    ⦃post⟨fun r => ⌜r.Nodup⌝, fun _ => ⌜False⌝, fun _msg state => ⌜state.counter = state.limit⌝⟩⦄ := by
  mvcgen [mkFreshN2] invariants
  · post⟨fun ⟨xs, acc⟩ state => ⌜(∀ n ∈ acc, n < state.counter) ∧ acc.toList.Nodup⌝,
         fun _ => ⌜False⌝,
         fun _msg state => ⌜state.counter = state.limit⌝⟩
  with grind
