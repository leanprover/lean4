-- These can move to Init after a stage0 update
open Lean.Order in
attribute [partial_fixpoint_monotone]
  monotone_ite
  monotone_dite
  monotone_bind
  monotone_mapM
  monotone_mapFinIdxM


/-!
Johannes Hölzl pointed out that the `partial_fixpoint` machinery can be applied to `Prop` to define
inductive or (when using the dual order) coinductive predicates.

Without an induction principle this isn't so useful, though.
-/

open Lean.Order

instance : Order Prop where
  rel x y := y → x -- NB: Dual
  rel_refl := fun x => x
  rel_trans h₁ h₂ := fun x => h₁ (h₂ x)
  rel_antisymm h₁ h₂ := propext ⟨h₂, h₁⟩

instance : CCPO Prop where
  csup c := ∀ p, c p → p
  csup_spec := fun _ =>
    ⟨fun h y hcy hx => h hx y hcy, fun h hx y hcy => h y hcy hx ⟩

def univ (n : Nat) : Prop :=
  univ (n + 1)
partial_fixpoint
