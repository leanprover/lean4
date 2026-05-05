/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladimir Gladshtein, Sebastian Graf
-/
module

prelude
public import Std.Internal.Do.Assertion

public section

namespace Lean.Order

universe u

variable {α : Type u} [CompleteLattice α]

/--
A complete lattice is a *frame* if binary meet distributes over arbitrary joins
(the frame law). This matches the Mathlib definition `Order.Frame`.

We keep `CompleteLattice` as a parameter (instead of extending it), so the class only
adds the frame law.
-/
class Frame (α : Type u) [CompleteLattice α] : Prop where
  meet_sup (a : α) (s : α → Prop) :
    a ⊓ CompleteLattice.sup s =
      CompleteLattice.sup (fun y => ∃ x, s x ∧ y = a ⊓ x)

/--
Heyting implication in a frame, defined as the join of all `x` such that `a ⊓ x ⊑ b`.
-/
noncomputable def himp (a b : α) : α := CompleteLattice.sup (fun x => a ⊓ x ⊑ b)

scoped infixr:60 " ⇨ " => himp

/-- `a ⇨ b` is the least upper bound of `{x | a ⊓ x ⊑ b}` by definition. -/
theorem himp_spec (a b : α) : is_sup (fun x : α => a ⊓ x ⊑ b) (a ⇨ b) := by
  exact CompleteLattice.sup_spec (fun x : α => a ⊓ x ⊑ b)

/--
Completeness direction that only needs `CompleteLattice`:
if `a ⊓ x ⊑ b`, then `x ⊑ a ⇨ b`.
-/
theorem himp_complete (x a b : α) : a ⊓ x ⊑ b → x ⊑ a ⇨ b := by
  intro h
  exact le_sup (c := fun y : α => a ⊓ y ⊑ b) h

/--
Soundness direction (`a ⊓ (a ⇨ b) ⊑ b`) from the frame distributivity law.
-/
theorem himp_sound [Frame α] (a b : α) : a ⊓ (a ⇨ b) ⊑ b := by
  let s : α → Prop := fun x => a ⊓ x ⊑ b
  change a ⊓ CompleteLattice.sup s ⊑ b
  rw [Frame.meet_sup (α := α) (a := a) (s := s)]
  apply sup_le
  intro y hy
  rcases hy with ⟨x, hx, rfl⟩
  exact hx

@[simp] theorem himp_prop_eq_imp (a b : Prop) : ((a ⇨ b : Prop) = (a → b)) := by
  apply propext
  constructor
  · intro hab
    have hs : (a ⇨ b : Prop) ⊑ (a → b) := by
      apply sup_le
      intro x hx hxTrue haTrue
      have hax : a ⊓ x := by
        simpa [meet_prop_eq_and] using (And.intro haTrue hxTrue)
      exact hx hax
    exact hs hab
  · intro hab
    have hx : a ⊓ (a → b) ⊑ b := by
      intro hax
      have hax' : a ∧ (a → b) := by
        simpa [meet_prop_eq_and] using hax
      exact hax'.right hax'.left
    exact (himp_complete (x := (a → b)) (a := a) (b := b) hx) hab

/-- Pointwise characterization of Heyting implication on function lattices. -/
@[simp] theorem himp_fun_apply
    {σ : Type v} {β : Type u} [CompleteLattice β]
    (a b : σ → β) (s : σ) :
    (a ⇨ b) s = (a s ⇨ b s) := by
  classical
  unfold himp
  rw [sup_fun_apply]
  apply PartialOrder.rel_antisymm
  · apply sup_le
    intro y ⟨f, hf, hfs⟩
    rw [← hfs]
    have hsf : a s ⊓ f s ⊑ b s := by
      simpa [meet_fun_apply] using (hf s)
    exact le_sup (c := fun z : β => a s ⊓ z ⊑ b s) hsf
  · apply sup_le
    intro y hy
    let f : σ → β := fun t => if t = s then y else ⊥
    have hf : a ⊓ f ⊑ b := by
      intro t
      simp only [meet_fun_apply, f]
      split
      · next h => subst h; exact hy
      · exact PartialOrder.rel_trans (meet_le_right ..) (bot_le ..)
    have hs : f s = y := by simp [f]
    exact le_sup (c := fun z => ∃ g, (a ⊓ g ⊑ b) ∧ g s = z) ⟨f, hf, hs⟩

end Lean.Order

end -- public section
