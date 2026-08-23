import Std.Tactic.Do
set_option warn.sorry false
open Lean.Order

opaque T : Type
instance : PartialOrder T := sorry

theorem nondep_le {σ α : Type u} [PartialOrder α] {f g : σ → α} :
    (∀ x, f x ⊑ g x) → f ⊑ g := fun h => h

theorem dep_le {σ : Sort u} {α : σ → Sort v} [∀ x, PartialOrder (α x)]
    {f g : (x : σ) → α x} : (∀ x, f x ⊑ g x) → f ⊑ g := fun h => h

#guard_msgs (error) in
example (a b : Nat → T) : a ⊑ b := by
  sym => apply nondep_le; sorry

#guard_msgs (error) in
example (a b : Nat → T) : a ⊑ b := by
  sym => apply dep_le; sorry

example (a b : Nat → T) : a ⊑ b := by
  with_reducible apply dep_le
  all_goals sorry
