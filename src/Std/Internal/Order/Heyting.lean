/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladimir Gladshtein, Sebastian Graf
-/
module

prelude
public import Std.Internal.Order.OfProp
public import Std.Internal.Order.PreservesSup
public import Init.ByCases
import Init.Classical

@[expose] public section

/-!
# Heyting implication

`a ⇨ b` is the upper adjoint of the lattice meet `a ⊓ ·`. A complete lattice whose meet preserves
suprema is a frame, and `⇨` then satisfies the laws of an implication: modus ponens, currying and
distribution of `⊓` over `⊔`.
-/

namespace Lean.Order

open PartialOrder Std.Internal.Order

universe u v

section Basic

variable {α : Type u} [CompleteLattice α]
/-- Unit for `⇨`, the meet specialization of `PreservesSup.le_upperAdjoint`: `a ⊓ x ⊑ b → x ⊑ a ⇨ b`. -/
theorem le_himp_of_meet_le_left {a b x : α} (h : a ⊓ x ⊑ b) : x ⊑ a ⇨ b := by
  unfold himp; exact PreservesSup.le_upperAdjoint (meet a) h

/-- Counit for `⇨`, the meet specialization of `PreservesSup.upperAdjoint_le`: `a ⊓ (a ⇨ b) ⊑ b`. -/
theorem meet_himp_le {a b : α} [PreservesSup (meet a)] : a ⊓ (a ⇨ b) ⊑ b := by
  unfold himp; exact PreservesSup.upperAdjoint_le (meet a) b
end Basic

/-! ## Derived laws -/

section Derived

set_option linter.unusedSectionVars false

variable {l : Type u} [CompleteLattice l] {P P' Q Q' R R' T : l} {φ φ₁ φ₂ : Prop}
variable [Heyting l]

/-! ### Connectives -/

theorem le_himp (h : P ⊓ Q ⊑ R) : P ⊑ Q ⇨ R :=
  le_himp_of_meet_le_left (rel_trans meet_le_comm h)
theorem meet_le_of_le_himp (h : P ⊑ Q ⇨ R) : P ⊓ Q ⊑ R := rel_trans
  (le_meet _ _ _ (meet_le_right _ _) (meet_le_of_left_le h))
  meet_himp_le
theorem meet_le_of_le_himp_left (h : Q ⊑ P ⇨ R) : P ⊓ Q ⊑ R :=
  rel_trans meet_le_comm (meet_le_of_le_himp h)
theorem himp_meet_le : (P ⇨ Q) ⊓ P ⊑ Q := meet_le_of_le_himp rel_refl
theorem le_himp_mp (h₁ : P ⊑ Q ⇨ R) (h₂ : P ⊑ Q) : P ⊑ R :=
  le_of_le_of_meet_le h₂ (meet_le_of_le_himp h₁)

theorem join_meet_le (hleft : P ⊓ R ⊑ T) (hright : Q ⊓ R ⊑ T) : (P ⊔ Q) ⊓ R ⊑ T :=
  meet_le_of_le_himp
    (join_le _ _ _ (le_himp hleft) (le_himp hright))
theorem meet_join_le (hleft : P ⊓ Q ⊑ T) (hright : P ⊓ R ⊑ T) : P ⊓ (Q ⊔ R) ⊑ T :=
  meet_le_of_le_himp_left
    (join_le _ _ _
      (le_himp (rel_trans meet_le_comm hleft))
      (le_himp (rel_trans meet_le_comm hright)))

/-! ### Monotonicity -/

theorem himp_mono (h1 : Q ⊑ P) (h2 : P' ⊑ Q') : (P ⇨ P') ⊑ Q ⇨ Q' :=
  le_himp <| rel_trans (meet_mono_right h1) <| rel_trans himp_meet_le h2
theorem himp_mono_left (h : P' ⊑ P) : (P ⇨ Q) ⊑ (P' ⇨ Q) := himp_mono h rel_refl
theorem himp_mono_right (h : Q ⊑ Q') : (P ⇨ Q) ⊑ (P ⇨ Q') := himp_mono rel_refl h

/-! ### Distributivity -/

theorem meet_join_left : P ⊓ (Q ⊔ R) = (P ⊓ Q) ⊔ (P ⊓ R) :=
  rel_antisymm
    (meet_join_le (le_join_of_le_left rel_refl) (le_join_of_le_right rel_refl))
    (join_le _ _ _ (meet_mono_right (left_le_join _ _)) (meet_mono_right (right_le_join _ _)))
theorem join_meet_left : P ⊔ (Q ⊓ R) = (P ⊔ Q) ⊓ (P ⊔ R) :=
  rel_antisymm
    (join_le _ _ _ (le_meet _ _ _ (left_le_join _ _) (left_le_join _ _))
      (meet_mono (right_le_join _ _) (right_le_join _ _)))
    (join_meet_le (le_join_of_le_left (meet_le_left _ _))
      (meet_join_le (le_join_of_le_left (meet_le_right _ _)) (le_join_of_le_right rel_refl)))
theorem meet_join_right : (P ⊔ Q) ⊓ R = (P ⊓ R) ⊔ (Q ⊓ R) :=
  meet_comm.trans (meet_join_left.trans (rel_antisymm
    (join_mono (P := _) (Q := _) (P' := _) (Q' := _)
      (rel_of_eq meet_comm) (rel_of_eq meet_comm))
    (join_mono (rel_of_eq meet_comm) (rel_of_eq meet_comm))))
theorem join_meet_right : (P ⊓ Q) ⊔ R = (P ⊔ R) ⊓ (Q ⊔ R) :=
  join_comm.trans (join_meet_left.trans (rel_antisymm
    (meet_mono (rel_of_eq join_comm) (rel_of_eq join_comm))
    (meet_mono (rel_of_eq join_comm) (rel_of_eq join_comm))))

/-! ### Units and composition -/

theorem top_himp : ((⊤ : l) ⇨ P) = P :=
  rel_antisymm
    (rel_trans (le_meet _ _ _ (le_top _) rel_refl) meet_himp_le)
    (le_himp (meet_le_of_left_le rel_refl))
theorem le_himp_self : Q ⊑ P ⇨ P := le_himp (meet_le_right _ _)
theorem le_himp_self_iff : (Q ⊑ P ⇨ P) ↔ True := iff_true_intro le_himp_self
theorem himp_meet_himp_le : (P ⇨ Q) ⊓ (Q ⇨ R) ⊑ P ⇨ R :=
  le_himp_of_meet_le_left <|
    rel_trans (rel_of_eq meet_assoc.symm) <|
      rel_trans (meet_mono_left meet_himp_le) meet_himp_le
theorem bot_himp : ((⊥ : l) ⇨ P) = ⊤ :=
  rel_antisymm (le_top _) (le_himp (meet_le_of_right_le (bot_le _)))

theorem meet_himp_le_meet : P' ⊓ (P' ⇨ Q') ⊑ P' ⊓ Q' :=
  le_meet _ _ _ (meet_le_left _ _) (rel_trans meet_le_comm himp_meet_le)
theorem meet_le_meet_of_le_himp (hp : P ⊑ P') (hq : Q ⊑ (P' ⇨ Q')) : P ⊓ Q ⊑ P' ⊓ Q' :=
  rel_trans (meet_mono hp hq) meet_himp_le_meet

/-! ### Interaction with the propositional embedding -/

theorem CompleteLattice.ofProp_imp_le_himp {φ₁ φ₂ : Prop} : (⌜φ₁ → φ₂⌝ : l) ⊑ (⌜φ₁⌝ ⇨ ⌜φ₂⌝) :=
  le_himp (rel_trans (rel_of_eq ofProp_meet_ofProp) (ofProp_mono (And.elim id)))

theorem CompleteLattice.ofProp_himp_ofProp {φ₁ φ₂ : Prop} : ((⌜φ₁⌝ : l) ⇨ ⌜φ₂⌝) = ⌜φ₁ → φ₂⌝ := by
  apply rel_antisymm
  · by_cases h₁ : φ₁
    · -- φ₁ true: weaken the LHS to `(⌜φ₁⌝ ⇨ ⌜φ₂⌝) ⊓ ⌜φ₁⌝` and apply `himp_meet_le`.
      have h₁' : (⊤ : l) ⊑ ⌜φ₁⌝ := by
        have : (⌜φ₁⌝ : l) = ⊤ := ofProp_eq_top h₁
        exact this ▸ rel_refl
      exact rel_trans
        (le_meet _ _ _ rel_refl (rel_trans (le_top _) h₁'))
        (rel_trans himp_meet_le (ofProp_mono (fun h _ => h)))
    · -- φ₁ false: `⌜φ₁ → φ₂⌝ = ⊤`
      have : (⌜φ₁ → φ₂⌝ : l) = ⊤ := ofProp_eq_top (fun hp => absurd hp h₁)
      exact this ▸ le_top _
  · exact ofProp_imp_le_himp

@[deprecated CompleteLattice.ofProp_imp_le_himp (since := "2026-09-24")]
theorem himp_ofProp_le {φ₁ φ₂ : Prop} : (⌜φ₁ → φ₂⌝ : l) ⊑ (⌜φ₁⌝ ⇨ ⌜φ₂⌝) :=
  CompleteLattice.ofProp_imp_le_himp
@[deprecated CompleteLattice.ofProp_himp_ofProp (since := "2026-09-24")]
theorem himp_ofProp {φ₁ φ₂ : Prop} : ((⌜φ₁⌝ : l) ⇨ ⌜φ₂⌝) = ⌜φ₁ → φ₂⌝ :=
  CompleteLattice.ofProp_himp_ofProp

@[deprecated join_meet_le (since := "2026-09-24")]
theorem meet_join_le_left (hleft : P ⊓ R ⊑ T) (hright : Q ⊓ R ⊑ T) : (P ⊔ Q) ⊓ R ⊑ T :=
  join_meet_le hleft hright
@[deprecated meet_join_le (since := "2026-09-24")]
theorem meet_join_le_right (hleft : P ⊓ Q ⊑ T) (hright : P ⊓ R ⊑ T) : P ⊓ (Q ⊔ R) ⊑ T :=
  meet_join_le hleft hright
@[deprecated le_himp (since := "2026-09-24")]
theorem le_himp_comm (h : P ⊓ Q ⊑ R) : P ⊑ Q ⇨ R := le_himp h
@[deprecated le_himp_of_meet_le_left +typeChanged (since := "2026-09-24")]
theorem le_himp_of_meet_le_comm (h : Q ⊓ P ⊑ R) : P ⊑ Q ⇨ R := le_himp_of_meet_le_left h
@[deprecated meet_le_of_le_himp_left (since := "2026-09-24")]
theorem meet_le_of_le_himp_comm (h : Q ⊑ P ⇨ R) : P ⊓ Q ⊑ R := meet_le_of_le_himp_left h

end Derived

/-- `⊤ ⊑ (P ⇨ Q)` iff `P ⊑ Q`. -/
theorem top_le_himp_iff {l : Type u} [CompleteLattice l]
    [Heyting l] (P Q : l) :
    ((⊤ : l) ⊑ P ⇨ Q) ↔ (P ⊑ Q) :=
  ⟨fun h => rel_trans
    (le_meet _ _ _ (le_top _) rel_refl)
    (rel_trans (meet_mono_left h) himp_meet_le),
   fun h => le_himp (meet_le_of_right_le h)⟩

end Lean.Order

end -- public section
