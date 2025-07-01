/-
Copyright (c) 2022 Lars König. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars König, Mario Carneiro, Sebastian Graf
-/
prelude
import Init.ByCases
import Std.Do.SPred.Laws

/-!
# Derived laws of `SPred`

This module contains some laws about `SPred` that are derived from
the laws in `Std.Do.Laws`.
-/

namespace Std.Do.SPred

variable {σs : List Type} {P P' Q Q' R R' : SPred σs} {φ φ₁ φ₂ : Prop}

theorem entails.rfl {σs : List Type} {P : SPred σs} : P ⊢ₛ P := entails.refl P

theorem bientails.rfl {σs : List Type} {P : SPred σs} : P ⊣⊢ₛ P := bientails.refl P
theorem bientails.of_eq {σs : List Type} {P Q : SPred σs} (h : P = Q) : P ⊣⊢ₛ Q := h ▸ .rfl

theorem bientails.mp {σs : List Type} {P Q : SPred σs} : (P ⊣⊢ₛ Q) → (P ⊢ₛ Q) := fun h => (bientails.iff.mp h).1
theorem bientails.mpr {σs : List Type} {P Q : SPred σs} : (P ⊣⊢ₛ Q) → (Q ⊢ₛ P) := fun h => (bientails.iff.mp h).2

/-! # Connectives -/

theorem and_elim_l' (h : P ⊢ₛ R) : P ∧ Q ⊢ₛ R := and_elim_l.trans h
theorem and_elim_r' (h : Q ⊢ₛ R) : P ∧ Q ⊢ₛ R := and_elim_r.trans h
theorem or_intro_l' (h : P ⊢ₛ Q) : P ⊢ₛ Q ∨ R := h.trans or_intro_l
theorem or_intro_r' (h : P ⊢ₛ R) : P ⊢ₛ Q ∨ R := h.trans or_intro_r
theorem and_symm : P ∧ Q ⊢ₛ Q ∧ P := and_intro and_elim_r and_elim_l
theorem or_symm : P ∨ Q ⊢ₛ Q ∨ P := or_elim or_intro_r or_intro_l
theorem imp_intro' (h : Q ∧ P ⊢ₛ R) : P ⊢ₛ Q → R := imp_intro <| and_symm.trans h
theorem entails.trans' (h₁ : P ⊢ₛ Q) (h₂ : P ∧ Q ⊢ₛ R) : P ⊢ₛ R := (and_intro .rfl h₁).trans h₂
theorem mp (h₁ : P ⊢ₛ Q → R) (h₂ : P ⊢ₛ Q) : P ⊢ₛ R := entails.trans' h₂ (imp_elim h₁)
theorem imp_elim' (h : Q ⊢ₛ P → R) : P ∧ Q ⊢ₛ R := and_symm.trans <| imp_elim h
theorem imp_elim_l : (P → Q) ∧ P ⊢ₛ Q := imp_elim .rfl
theorem imp_elim_r : P ∧ (P → Q) ⊢ₛ Q := imp_elim' .rfl
theorem false_elim : ⌜False⌝ ⊢ₛ P := pure_elim' False.elim
theorem true_intro : P ⊢ₛ ⌜True⌝ := pure_intro trivial
theorem exists_intro' {σs} {P} {Ψ : α → SPred σs} (a : α) (h : P ⊢ₛ Ψ a) : P ⊢ₛ ∃ a, Ψ a := h.trans (exists_intro a)
theorem and_or_elim_l (hleft : P ∧ R ⊢ₛ T) (hright : Q ∧ R ⊢ₛ T) : (P ∨ Q) ∧ R ⊢ₛ T := imp_elim (or_elim (imp_intro hleft) (imp_intro hright))
theorem and_or_elim_r (hleft : P ∧ Q ⊢ₛ T) (hright : P ∧ R ⊢ₛ T) : P ∧ (Q ∨ R) ⊢ₛ T := imp_elim' (or_elim (imp_intro (and_symm.trans hleft)) (imp_intro (and_symm.trans hright)))
theorem exfalso (h : P ⊢ₛ ⌜False⌝) : P ⊢ₛ Q := h.trans false_elim

/-! # Monotonicity and congruence -/

theorem and_mono (hp : P ⊢ₛ P') (hq : Q ⊢ₛ Q') : P ∧ Q ⊢ₛ P' ∧ Q' := and_intro (and_elim_l' hp) (and_elim_r' hq)
theorem and_mono_l (h : P ⊢ₛ P') : P ∧ Q ⊢ₛ P' ∧ Q := and_mono h .rfl
theorem and_mono_r (h : Q ⊢ₛ Q') : P ∧ Q ⊢ₛ P ∧ Q' := and_mono .rfl h
theorem and_congr (hp : P ⊣⊢ₛ P') (hq : Q ⊣⊢ₛ Q') : P ∧ Q ⊣⊢ₛ P' ∧ Q' := bientails.iff.mpr ⟨and_mono (bientails.mp hp) (bientails.mp hq), and_mono (bientails.mpr hp) (bientails.mpr hq)⟩
theorem and_congr_l (hp : P ⊣⊢ₛ P') : P ∧ Q ⊣⊢ₛ P' ∧ Q := and_congr hp .rfl
theorem and_congr_r (hq : Q ⊣⊢ₛ Q') : P ∧ Q ⊣⊢ₛ P ∧ Q' := and_congr .rfl hq
theorem or_mono (hp : P ⊢ₛ P') (hq : Q ⊢ₛ Q') : P ∨ Q ⊢ₛ P' ∨ Q' := or_elim (or_intro_l' hp) (or_intro_r' hq)
theorem or_mono_l (h : P ⊢ₛ P') : P ∨ Q ⊢ₛ P' ∨ Q := or_mono h .rfl
theorem or_mono_r (h : Q ⊢ₛ Q') : P ∨ Q ⊢ₛ P ∨ Q' := or_mono .rfl h
theorem or_congr (hp : P ⊣⊢ₛ P') (hq : Q ⊣⊢ₛ Q') : P ∨ Q ⊣⊢ₛ P' ∨ Q' := bientails.iff.mpr ⟨or_mono (bientails.mp hp) (bientails.mp hq), or_mono (bientails.mpr hp) (bientails.mpr hq)⟩
theorem or_congr_l (hp : P ⊣⊢ₛ P') : P ∨ Q ⊣⊢ₛ P' ∨ Q := or_congr hp .rfl
theorem or_congr_r (hq : Q ⊣⊢ₛ Q') : P ∨ Q ⊣⊢ₛ P ∨ Q' := or_congr .rfl hq
theorem imp_mono (h1 : Q ⊢ₛ P) (h2 : P' ⊢ₛ Q') : (P → P') ⊢ₛ Q → Q' := imp_intro <| (and_mono_r h1).trans <| (imp_elim .rfl).trans h2
theorem imp_mono_l (h : P' ⊢ₛ P) : (P → Q) ⊢ₛ (P' → Q) := imp_mono h .rfl
theorem imp_mono_r (h : Q ⊢ₛ Q') : (P → Q) ⊢ₛ (P → Q') := imp_mono .rfl h
theorem imp_congr (h1 : P ⊣⊢ₛ Q) (h2 : P' ⊣⊢ₛ Q') : (P → P') ⊣⊢ₛ (Q → Q') := bientails.iff.mpr ⟨imp_mono h1.mpr h2.mp, imp_mono h1.mp h2.mpr⟩
theorem imp_congr_l (h : P ⊣⊢ₛ P') : (P → Q) ⊣⊢ₛ (P' → Q) := imp_congr h .rfl
theorem imp_congr_r (h : Q ⊣⊢ₛ Q') : (P → Q) ⊣⊢ₛ (P → Q') := imp_congr .rfl h
theorem forall_mono {Φ Ψ : α → SPred σs} (h : ∀ a, Φ a ⊢ₛ Ψ a) : (∀ a, Φ a) ⊢ₛ ∀ a, Ψ a := forall_intro fun a => (forall_elim a).trans (h a)
theorem forall_congr {Φ Ψ : α → SPred σs} (h : ∀ a, Φ a ⊣⊢ₛ Ψ a) : (∀ a, Φ a) ⊣⊢ₛ ∀ a, Ψ a := bientails.iff.mpr ⟨forall_mono fun a => (h a).mp, forall_mono fun a => (h a).mpr⟩
theorem exists_mono {Φ Ψ : α → SPred σs} (h : ∀ a, Φ a ⊢ₛ Ψ a) : (∃ a, Φ a) ⊢ₛ ∃ a, Ψ a := exists_elim fun a => (h a).trans (exists_intro a)
theorem exists_congr {Φ Ψ : α → SPred σs} (h : ∀ a, Φ a ⊣⊢ₛ Ψ a) : (∃ a, Φ a) ⊣⊢ₛ ∃ a, Ψ a := bientails.iff.mpr ⟨exists_mono fun a => (h a).mp, exists_mono fun a => (h a).mpr⟩

theorem and_imp (hp : P₁ ⊢ₛ P₂) (hq : Q₁ ⊢ₛ Q₂) : (P₁ ∧ Q₁) ⊢ₛ (P₂ ∧ Q₂) := and_intro (and_elim_l' hp) (and_elim_r' hq)
theorem or_imp_left (hleft : P₁ ⊢ₛ P₂) : (P₁ ∨ Q) ⊢ₛ (P₂ ∨ Q) := or_elim (or_intro_l' hleft) or_intro_r
theorem or_imp_right (hright : Q₁ ⊢ₛ Q₂) : (P ∨ Q₁) ⊢ₛ (P ∨ Q₂) := or_elim or_intro_l (or_intro_r' hright)

/-! # Boolean algebra -/

theorem and_self : P ∧ P ⊣⊢ₛ P := bientails.iff.mpr ⟨and_elim_l, and_intro .rfl .rfl⟩
theorem or_self : P ∨ P ⊣⊢ₛ P := bientails.iff.mpr ⟨or_elim .rfl .rfl, or_intro_l⟩
theorem and_comm : P ∧ Q ⊣⊢ₛ Q ∧ P := bientails.iff.mpr ⟨and_symm, and_symm⟩
theorem or_comm : P ∨ Q ⊣⊢ₛ Q ∨ P := bientails.iff.mpr ⟨or_symm, or_symm⟩
theorem and_assoc : (P ∧ Q) ∧ R ⊣⊢ₛ P ∧ Q ∧ R := bientails.iff.mpr ⟨and_intro (and_elim_l' and_elim_l) (and_mono_l and_elim_r), and_intro (and_mono_r and_elim_l) (and_elim_r' and_elim_r)⟩
theorem or_assoc : (P ∨ Q) ∨ R ⊣⊢ₛ P ∨ Q ∨ R := bientails.iff.mpr ⟨or_elim (or_mono_r or_intro_l) (or_intro_r' or_intro_r), or_elim (or_intro_l' or_intro_l) (or_mono_l or_intro_r)⟩
theorem and_eq_right : (P ⊢ₛ Q) ↔ P ⊣⊢ₛ Q ∧ P := Iff.intro (fun h => bientails.iff.mpr ⟨and_intro h .rfl, and_elim_r⟩) (fun h => h.mp.trans and_elim_l)
theorem and_eq_left : (P ⊢ₛ Q) ↔ P ⊣⊢ₛ P ∧ Q := Iff.intro (fun h => bientails.iff.mpr ⟨and_intro .rfl h, and_elim_l⟩) (fun h => h.mp.trans and_elim_r)
theorem or_eq_left : (P ⊢ₛ Q) ↔ Q ⊣⊢ₛ Q ∨ P := Iff.intro (fun h => bientails.iff.mpr ⟨or_intro_l' .rfl, or_elim .rfl h⟩) (fun h => or_intro_r.trans h.mpr)
theorem or_eq_right : (P ⊢ₛ Q) ↔ Q ⊣⊢ₛ P ∨ Q := Iff.intro (fun h => bientails.iff.mpr ⟨or_intro_r' .rfl, or_elim h .rfl⟩) (fun h => or_intro_l.trans h.mpr)

theorem and_or_left : P ∧ (Q ∨ R) ⊣⊢ₛ (P ∧ Q) ∨ (P ∧ R) :=
  bientails.iff.mpr ⟨and_or_elim_r or_intro_l or_intro_r,
                     or_elim (and_intro and_elim_l (or_intro_l' and_elim_r)) (and_intro and_elim_l (or_intro_r' and_elim_r))⟩
theorem or_and_left : P ∨ (Q ∧ R) ⊣⊢ₛ (P ∨ Q) ∧ (P ∨ R) :=
  bientails.iff.mpr ⟨or_elim (and_intro or_intro_l or_intro_l) (and_imp or_intro_r or_intro_r),
                     and_or_elim_l (or_intro_l' and_elim_l) (and_or_elim_r (or_intro_l' and_elim_r) or_intro_r)⟩
theorem or_and_right : (P ∨ Q) ∧ R ⊣⊢ₛ (P ∧ R) ∨ (Q ∧ R) := and_comm.trans (and_or_left.trans (or_congr and_comm and_comm))
theorem and_or_right : (P ∧ Q) ∨ R ⊣⊢ₛ (P ∨ R) ∧ (Q ∨ R) := or_comm.trans (or_and_left.trans (and_congr or_comm or_comm))

theorem true_and : ⌜True⌝ ∧ P ⊣⊢ₛ P := bientails.iff.mpr ⟨and_elim_r, and_intro (pure_intro trivial) .rfl⟩
theorem and_true : P ∧ ⌜True⌝ ⊣⊢ₛ P := and_comm.trans true_and
theorem false_and : ⌜False⌝ ∧ P ⊣⊢ₛ ⌜False⌝ := bientails.iff.mpr ⟨and_elim_l, false_elim⟩
theorem and_false : P ∧ ⌜False⌝ ⊣⊢ₛ ⌜False⌝ := and_comm.trans false_and
theorem true_or : ⌜True⌝ ∨ P ⊣⊢ₛ ⌜True⌝ := bientails.iff.mpr ⟨true_intro, or_intro_l⟩
theorem or_true : P ∨ ⌜True⌝ ⊣⊢ₛ ⌜True⌝ := or_comm.trans true_or
theorem false_or : ⌜False⌝ ∨ P ⊣⊢ₛ P := bientails.iff.mpr ⟨or_elim false_elim .rfl, or_intro_r⟩
theorem or_false : P ∨ ⌜False⌝ ⊣⊢ₛ P := or_comm.trans false_or

theorem true_imp : (⌜True⌝ → P) ⊣⊢ₛ P := bientails.iff.mpr ⟨and_true.mpr.trans imp_elim_l, imp_intro and_elim_l⟩
theorem imp_self : Q ⊢ₛ P → P := imp_intro and_elim_r
theorem imp_self_simp : (Q ⊢ₛ P → P) ↔ True := iff_true_intro imp_self
theorem imp_trans : (P → Q) ∧ (Q → R) ⊢ₛ P → R := imp_intro' <| and_assoc.mpr.trans <| (and_mono_l imp_elim_r).trans imp_elim_r
theorem false_imp : (⌜False⌝ → P) ⊣⊢ₛ ⌜True⌝ := bientails.iff.mpr ⟨true_intro, imp_intro <| and_elim_r.trans false_elim⟩

/-! # Pure -/

theorem pure_elim {φ : Prop} (h1 : Q ⊢ₛ ⌜φ⌝) (h2 : φ → Q ⊢ₛ R) : Q ⊢ₛ R :=
  and_self.mpr.trans <| imp_elim <| h1.trans <| pure_elim' fun h =>
    imp_intro' <| and_elim_l.trans (h2 h)

theorem pure_mono {φ₁ φ₂ : Prop} (h : φ₁ → φ₂) : ⌜φ₁⌝ ⊢ₛ (⌜φ₂⌝ : SPred σs) := pure_elim' <| pure_intro ∘ h
theorem pure_congr {φ₁ φ₂ : Prop} (h : φ₁ ↔ φ₂) : ⌜φ₁⌝ ⊣⊢ₛ (⌜φ₂⌝ : SPred σs) := bientails.iff.mpr ⟨pure_mono h.1, pure_mono h.2⟩

theorem pure_elim_l {φ : Prop} (h : φ → Q ⊢ₛ R) : ⌜φ⌝ ∧ Q ⊢ₛ R := pure_elim and_elim_l <| and_elim_r' ∘ h
theorem pure_elim_r {φ : Prop} (h : φ → Q ⊢ₛ R) : Q ∧ ⌜φ⌝ ⊢ₛ R := and_comm.mp.trans (pure_elim_l h)
theorem pure_true {φ : Prop} (h : φ) : ⌜φ⌝ ⊣⊢ₛ (⌜True⌝ : SPred σs) := eq_true h ▸ .rfl
theorem pure_and {φ₁ φ₂ : Prop} : ⌜φ₁⌝ ∧ (⌜φ₂⌝ : SPred σs) ⊣⊢ₛ ⌜φ₁ ∧ φ₂⌝ := bientails.iff.mpr ⟨pure_elim and_elim_l fun h => and_elim_r' <| pure_mono <| And.intro h, and_intro (pure_mono And.left) (pure_mono And.right)⟩
theorem pure_or {φ₁ φ₂ : Prop} : ⌜φ₁⌝ ∨ (⌜φ₂⌝ : SPred σs) ⊣⊢ₛ ⌜φ₁ ∨ φ₂⌝ := bientails.iff.mpr ⟨or_elim (pure_mono Or.inl) (pure_mono Or.inr), pure_elim' (·.elim (or_intro_l' ∘ pure_intro) (or_intro_r' ∘ pure_intro))⟩
theorem pure_imp_2 {φ₁ φ₂ : Prop} : ⌜φ₁ → φ₂⌝ ⊢ₛ (⌜φ₁⌝ → ⌜φ₂⌝ : SPred σs) := imp_intro <| pure_and.mp.trans <| pure_mono (And.elim id)
theorem pure_imp {φ₁ φ₂ : Prop} : (⌜φ₁⌝ → ⌜φ₂⌝ : SPred σs) ⊣⊢ₛ ⌜φ₁ → φ₂⌝ := by
  refine bientails.iff.mpr ⟨?_, pure_imp_2⟩
  if h : φ₁
  then exact (mp .rfl (pure_intro h)).trans (pure_mono fun h _ => h)
  else exact pure_intro h.elim

theorem pure_forall_2 {φ : α → Prop} : ⌜∀ x, φ x⌝ ⊢ₛ ∀ x, (⌜φ x⌝ : SPred σs) := forall_intro fun _ => pure_mono (· _)
theorem pure_forall {φ : α → Prop} : (∀ x, (⌜φ x⌝ : SPred σs)) ⊣⊢ₛ ⌜∀ x, φ x⌝ := by
  refine bientails.iff.mpr ⟨?_, pure_forall_2⟩
  if h : ∃ x, ¬φ x
  then let ⟨x, h⟩ := h
       exact (forall_elim x).trans (pure_mono h.elim)
  else exact pure_intro fun x => Classical.not_not.1 <| mt (⟨x, ·⟩) h

theorem pure_exists {φ : α → Prop} : (∃ x, ⌜φ x⌝ : SPred σs) ⊣⊢ₛ ⌜∃ x, φ x⌝ := bientails.iff.mpr ⟨exists_elim fun a => pure_mono (⟨a, ·⟩), pure_elim' fun ⟨x, h⟩ => (pure_intro h).trans (exists_intro' x .rfl)⟩

@[simp] theorem true_intro_simp : (Q ⊢ₛ ⌜True⌝) ↔ True := iff_true_intro true_intro
@[simp] theorem true_intro_simp_nil {Q : SPred []} : (Q ⊢ₛ True) ↔ True := true_intro_simp

/-! # Miscellaneous -/

theorem and_left_comm : P ∧ Q ∧ R ⊣⊢ₛ Q ∧ P ∧ R := and_assoc.symm.trans <| (and_congr_l and_comm).trans and_assoc
theorem and_right_comm : (P ∧ Q) ∧ R ⊣⊢ₛ (P ∧ R) ∧ Q := and_assoc.trans <| (and_congr_r and_comm).trans and_assoc.symm

/-! # Working with entailment -/

theorem entails_pure_intro {σs : List Type} (P Q : Prop) (h : P → Q) : entails ⌜P⌝ (σs := σs) ⌜Q⌝ := pure_elim' fun hp => pure_intro (h hp)

@[simp] theorem entails_elim_nil (P Q : SPred []) : entails P Q ↔ P → Q := iff_of_eq rfl
theorem entails_elim_cons {σ : Type} {σs : List Type} (P Q : SPred (σ::σs)) : P ⊢ₛ Q ↔ ∀ s, (P s ⊢ₛ Q s) := by simp only [entails]
@[simp] theorem entails_pure_elim_cons {σ : Type} {σs : List Type} [Inhabited σ] (P Q : Prop) : entails ⌜P⌝ (σs := σ::σs) ⌜Q⌝ ↔ entails ⌜P⌝ (σs := σs) ⌜Q⌝:= by simp [entails]
@[simp] theorem entails_true_intro {σs : List Type} (P Q : SPred σs) : ⊢ₛ P → Q ↔ P ⊢ₛ Q := Iff.intro (fun h => (and_intro true_intro .rfl).trans (imp_elim h)) (fun h => imp_intro (and_elim_r.trans h))

/-! # Tactic support -/

namespace Tactic

/-- Tautology in `SPred` as a quotable definition. -/
abbrev tautological {σs : List Type} (Q : SPred σs) : Prop := ⊢ₛ Q

class PropAsSPredTautology (φ : Prop) {σs : outParam (List Type)} (P : outParam (SPred σs)) : Prop where
  iff : φ ↔ ⊢ₛ P
instance : PropAsSPredTautology (σs := []) φ φ where iff := true_imp_iff.symm
instance : PropAsSPredTautology (P ⊢ₛ Q) spred(P → Q) where iff := (entails_true_intro P Q).symm
instance : PropAsSPredTautology (⊢ₛ P) P where iff := Iff.rfl

class IsPure {σs : List Type} (P : SPred σs) (φ : outParam Prop) where to_pure : P ⊣⊢ₛ ⌜φ⌝
instance (σs) : IsPure (σs:=σs) ⌜φ⌝ φ where to_pure := .rfl
instance (σs) : IsPure (σs:=σs) spred(⌜φ⌝ → ⌜ψ⌝) (φ → ψ) where to_pure := pure_imp
instance (σs) : IsPure (σs:=σs) spred(⌜φ⌝ ∧ ⌜ψ⌝) (φ ∧ ψ) where to_pure := pure_and
instance (σs) : IsPure (σs:=σs) spred(⌜φ⌝ ∨ ⌜ψ⌝) (φ ∨ ψ) where to_pure := pure_or
instance (σs) (P : α → Prop) : IsPure (σs:=σs) spred(∃ x, ⌜P x⌝) (∃ x, P x) where to_pure := pure_exists
instance (σs) (P : α → Prop) : IsPure (σs:=σs) spred(∀ x, ⌜P x⌝) (∀ x, P x) where to_pure := pure_forall
instance (σs) (P : SPred (σ::σs)) [inst : IsPure P φ] : IsPure (σs:=σs) spred(P s) φ where to_pure := (iff_of_eq bientails_cons).mp inst.to_pure s
instance (P : Prop) : IsPure (σs:=[]) P P where to_pure := Iff.rfl

class IsAnd {σs : List Type} (P : SPred σs) (Q₁ Q₂ : outParam (SPred σs)) where
  to_and : P ⊣⊢ₛ Q₁ ∧ Q₂
instance (σs) (Q₁ Q₂ : SPred σs) : IsAnd (σs:=σs) spred(Q₁ ∧ Q₂) Q₁ Q₂ where to_and := .rfl
instance (σs) : IsAnd (σs:=σs) ⌜p ∧ q⌝ ⌜p⌝ ⌜q⌝ where to_and := pure_and.symm
instance (σs) (P Q₁ Q₂ : σ → SPred σs) [base : ∀ s, IsAnd (P s) (Q₁ s) (Q₂ s)] : IsAnd (σs:=σ::σs) P Q₁ Q₂ where to_and := fun s => (base s).to_and

theorem ProofMode.start_entails {φ : Prop} [PropAsSPredTautology φ P] : (⊢ₛ P) → φ := PropAsSPredTautology.iff.mpr
theorem ProofMode.elim_entails {φ : Prop} [PropAsSPredTautology φ P] : φ → (⊢ₛ P) := PropAsSPredTautology.iff.mp

theorem Assumption.left {σs : List Type} {P Q R : SPred σs} (h : P ⊢ₛ R) : P ∧ Q ⊢ₛ R := and_elim_l.trans h
theorem Assumption.right {σs : List Type} {P Q R : SPred σs} (h : Q ⊢ₛ R) : P ∧ Q ⊢ₛ R := and_elim_r.trans h
theorem SCases.add_goal {σs} {P Q H T : SPred σs} (hand : Q ∧ H ⊣⊢ₛ P) (hgoal : P ⊢ₛ T) : Q ∧ H ⊢ₛ T := hand.mp.trans hgoal
theorem SCases.clear {σs} {Q H T : SPred σs} (hgoal : Q ∧ ⌜True⌝ ⊢ₛ T) : Q ∧ H ⊢ₛ T := (and_mono_r true_intro).trans hgoal
theorem SCases.pure {σs} {Q T : SPred σs} (hgoal : Q ∧ ⌜True⌝ ⊢ₛ T) : Q ⊢ₛ T := (and_intro .rfl true_intro).trans hgoal
theorem SCases.and_1 {σs} {Q H₁' H₂' H₁₂' T : SPred σs} (hand : H₁' ∧ H₂' ⊣⊢ₛ H₁₂') (hgoal : Q ∧ H₁₂' ⊢ₛ T) : (Q ∧ H₁') ∧ H₂' ⊢ₛ T := ((and_congr_r hand.symm).trans and_assoc.symm).mpr.trans hgoal
theorem SCases.and_2 {σs} {Q H₁' H₂ T : SPred σs} (hgoal : (Q ∧ H₁') ∧ H₂ ⊢ₛ T) : (Q ∧ H₂) ∧ H₁' ⊢ₛ T := and_right_comm.mp.trans hgoal
theorem SCases.and_3 {σs} {Q H₁ H₂ H T : SPred σs} (hand : H ⊣⊢ₛ H₁ ∧ H₂) (hgoal : (Q ∧ H₂) ∧ H₁ ⊢ₛ T) : Q ∧ H ⊢ₛ T := (and_congr_r hand).mp.trans (and_assoc.mpr.trans (and_right_comm.mp.trans hgoal))
theorem SCases.exists {σs : List Type} {Q : SPred σs} {ψ : α → SPred σs} {T : SPred σs} (h : ∀ a, Q ∧ ψ a ⊢ₛ T) : Q ∧ (∃ a, ψ a) ⊢ₛ T := imp_elim' (exists_elim fun a => imp_intro (entails.trans and_symm (h a)))
theorem Clear.clear {σs : List Type} {P P' A Q : SPred σs} (hfocus : P ⊣⊢ₛ P' ∧ A) (h : P' ⊢ₛ Q) : P ⊢ₛ Q := hfocus.mp.trans <| (and_mono_l h).trans and_elim_l
theorem Exact.assumption {σs : List Type} {P P' A : SPred σs} (h : P ⊣⊢ₛ P' ∧ A) : P ⊢ₛ A := h.mp.trans and_elim_r
theorem Exact.from_tautology {σs : List Type} {P T : SPred σs} [PropAsSPredTautology φ T] (h : φ) : P ⊢ₛ T := true_intro.trans (PropAsSPredTautology.iff.mp h)
theorem Focus.this {σs : List Type} {P : SPred σs} : P ⊣⊢ₛ ⌜True⌝ ∧ P := true_and.symm
theorem Focus.left {σs : List Type} {P P' Q C R : SPred σs} (h₁ : P ⊣⊢ₛ P' ∧ R) (h₂ : P' ∧ Q ⊣⊢ₛ C) : P ∧ Q ⊣⊢ₛ C ∧ R := (and_congr_l h₁).trans (and_right_comm.trans (and_congr_l h₂))
theorem Focus.right {σs : List Type} {P Q Q' C R : SPred σs} (h₁ : Q ⊣⊢ₛ Q' ∧ R) (h₂ : P ∧ Q' ⊣⊢ₛ C) : P ∧ Q ⊣⊢ₛ C ∧ R := (and_congr_r h₁).trans (and_assoc.symm.trans (and_congr_l h₂))
theorem Focus.rewrite_hyps {σs} {P Q R : SPred σs} (hrw : P ⊣⊢ₛ Q) (hgoal : Q ⊢ₛ R) : P ⊢ₛ R := hrw.mp.trans hgoal
theorem Have.dup {σs : List Type} {P Q H T : SPred σs} (hfoc : P ⊣⊢ₛ Q ∧ H) (hgoal : P ∧ H ⊢ₛ T) : P ⊢ₛ T := (and_intro .rfl (hfoc.mp.trans and_elim_r)).trans hgoal
theorem Have.have {σs : List Type} {P H PH T : SPred σs} (hand : P ∧ H ⊣⊢ₛ PH) (hhave : P ⊢ₛ H) (hgoal : PH ⊢ₛ T) : P ⊢ₛ T := (and_intro .rfl hhave).trans (hand.mp.trans hgoal)
theorem Have.replace {σs : List Type} {P H H' PH PH' T : SPred σs} (hfoc : PH ⊣⊢ₛ P ∧ H ) (hand : P ∧ H' ⊣⊢ₛ PH') (hhave : PH ⊢ₛ H') (hgoal : PH' ⊢ₛ T) : PH ⊢ₛ T := (and_intro (hfoc.mp.trans and_elim_l) hhave).trans (hand.mp.trans hgoal)
theorem Intro.intro {σs : List Type} {P Q H T : SPred σs} (hand : Q ∧ H ⊣⊢ₛ P) (h : P ⊢ₛ T) : Q ⊢ₛ H → T := imp_intro (hand.mp.trans h)
theorem Pure.thm {σs : List Type} {P Q T : SPred σs} {φ : Prop} [IsPure Q φ] (h : φ → P ⊢ₛ T) : P ∧ Q ⊢ₛ T := by
  apply pure_elim
  · exact and_elim_r.trans IsPure.to_pure.mp
  · intro hp
    exact and_elim_l.trans (h hp)
/-- A generalization of `pure_intro` exploiting `IsPure`. -/
theorem Pure.intro {σs : List Type} {P Q : SPred σs} {φ : Prop} [IsPure Q φ] (hp : φ) : P ⊢ₛ Q := (pure_intro hp).trans IsPure.to_pure.mpr
theorem Revert.revert {σs : List Type} {P Q H T : SPred σs} (hfoc : P ⊣⊢ₛ Q ∧ H) (h : Q ⊢ₛ H → T) : P ⊢ₛ T := hfoc.mp.trans (imp_elim h)
theorem Specialize.imp_stateful {P P' Q R : SPred σs}
    (hrefocus : P ∧ (Q → R) ⊣⊢ₛ P' ∧ Q) : P ∧ (Q → R) ⊢ₛ P ∧ R := by
  calc spred(P ∧ (Q → R))
    _ ⊢ₛ (P' ∧ Q) ∧ (Q → R) := and_intro hrefocus.mp and_elim_r
    _ ⊢ₛ P' ∧ Q ∧ (Q → R) := and_assoc.mp
    _ ⊢ₛ P' ∧ Q ∧ R := and_mono_r (and_intro and_elim_l imp_elim_r)
    _ ⊢ₛ (P' ∧ Q) ∧ R := and_assoc.mpr
    _ ⊢ₛ P ∧ R := and_mono_l (hrefocus.mpr.trans and_elim_l)

theorem Specialize.imp_pure {P Q R : SPred σs} [PropAsSPredTautology φ Q]
    (h : φ) : P ∧ (Q → R) ⊢ₛ P ∧ R := by
  calc spred(P ∧ (Q → R))
    _ ⊢ₛ P ∧ (Q ∧ (Q → R)) := and_mono_r (and_intro (true_intro.trans (PropAsSPredTautology.iff.mp h)) .rfl)
    _ ⊢ₛ P ∧ R := and_mono_r (mp and_elim_r and_elim_l)

theorem Specialize.forall {P : SPred σs} {ψ : α → SPred σs} (a : α) : P ∧ (∀ x, ψ x) ⊢ₛ P ∧ ψ a := and_mono_r (forall_elim a)
theorem Specialize.pure_start {φ : Prop} {H P T : SPred σs} [PropAsSPredTautology φ H] (hpure : φ) (hgoal : P ∧ H ⊢ₛ T) : P ⊢ₛ T := (and_intro .rfl (true_intro.trans (PropAsSPredTautology.iff.mp hpure))).trans hgoal
theorem Specialize.pure_taut {σs} {φ} {P : SPred σs} [IsPure P φ] (h : φ) : ⊢ₛ P := (pure_intro h).trans IsPure.to_pure.mpr
theorem Specialize.focus {P P' Q R : SPred σs} (hfocus : P ⊣⊢ₛ P' ∧ Q) (hnew : P' ∧ Q ⊢ₛ R) : P ⊢ₛ R := hfocus.mp.trans hnew

class SimpAnd {σs : List Type} (P Q : SPred σs) (PQ : outParam (SPred σs)) : Prop where
  simp_and : P ∧ Q ⊣⊢ₛ PQ
instance (σs) (P Q : SPred σs) : SimpAnd P Q (spred(P ∧ Q)) where simp_and := .rfl
instance (σs) (P : SPred σs) : SimpAnd P ⌜True⌝ P where simp_and := and_true
instance (σs) (P : SPred σs) : SimpAnd ⌜True⌝ P P where simp_and := true_and

class HasFrame {σs : List Type} (P : SPred σs) (P' : outParam (SPred σs)) (φ : outParam Prop) : Prop where
  reassoc : P ⊣⊢ₛ P' ∧ ⌜φ⌝
instance (σs) : HasFrame (σs:=σs) ⌜φ⌝ ⌜True⌝ φ where reassoc := true_and.symm
instance (σs) (P P' Q QP : SPred σs) [HasFrame P Q φ] [SimpAnd Q P' QP]: HasFrame (σs:=σs) spred(P ∧ P') QP φ where reassoc := ((and_congr_l HasFrame.reassoc).trans and_right_comm).trans (and_congr_l SimpAnd.simp_and)
instance (σs) (P P' Q' PQ : SPred σs) [HasFrame P' Q' φ] [SimpAnd P Q' PQ]: HasFrame (σs:=σs) spred(P ∧ P') PQ φ where reassoc := ((and_congr_r HasFrame.reassoc).trans and_assoc.symm).trans (and_congr_l SimpAnd.simp_and)
instance (σs) (P : SPred σs) : HasFrame (σs:=σs) spred(⌜φ⌝ ∧ P) P φ where reassoc := and_comm
instance (σs) (P : SPred σs) : HasFrame (σs:=σs) spred(P ∧ ⌜φ⌝) P φ where reassoc := .rfl
instance (σs) (P P' Q Q' QQ : SPred σs) [HasFrame P Q φ] [HasFrame P' Q' ψ] [SimpAnd Q Q' QQ]: HasFrame (σs:=σs) spred(P ∧ P') QQ (φ ∧ ψ) where
  reassoc := (and_congr HasFrame.reassoc HasFrame.reassoc).trans
             <| and_assoc.trans
             <| (and_congr_r
                  <| and_assoc.symm.trans
                  <| (and_congr_l and_comm).trans
                  <| and_assoc.trans
                  <| and_congr_r pure_and).trans
             <| and_assoc.symm.trans
             <| and_congr_l SimpAnd.simp_and
instance (σs) (P Q : SPred σs) [HasFrame P Q ψ] : HasFrame (σs:=σs) spred(⌜φ⌝ ∧ P) Q (φ ∧ ψ) where
  reassoc := and_comm.trans
             <| (and_congr_l HasFrame.reassoc).trans
             <| and_right_comm.trans
             <| and_assoc.trans
             <| and_congr_r pure_and
instance (σs) (P Q : SPred σs) [HasFrame P Q ψ] : HasFrame (σs:=σs) spred(P ∧ ⌜φ⌝) Q (ψ ∧ φ) where
  reassoc := (and_congr_l HasFrame.reassoc).trans
             <| and_right_comm.trans
             <| and_assoc.trans
             <| and_congr_r (and_comm.trans pure_and)
-- The following instance comes last so that it gets the highest priority.
-- It's the most efficient and best solution if valid
instance {P : Prop} : HasFrame (σs:=[]) P ⌜True⌝ P where reassoc := true_and.symm

theorem Frame.frame {σs : List Type} {P Q T : SPred σs} {φ : Prop} [HasFrame P Q φ]
  (h : φ → Q ⊢ₛ T) : P ⊢ₛ T := by
    apply SPred.pure_elim
    · exact HasFrame.reassoc.mp.trans SPred.and_elim_r
    · intro hp
      exact HasFrame.reassoc.mp.trans (SPred.and_elim_l' (h hp))
