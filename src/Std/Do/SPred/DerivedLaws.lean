/-
Copyright (c) 2022 Lars König. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars König, Mario Carneiro, Sebastian Graf
-/
module

prelude
public import Init.ByCases
public import Std.Do.SPred.Laws

@[expose] public section

set_option linter.missingDocs true

/-!
# Derived laws of `SPred`

This module contains some laws about `SPred` that are derived from
the laws in `Std.Do.Laws`.
-/

namespace Std.Do.SPred

universe u
variable {σs : List (Type u)} {P P' Q Q' R R' : SPred σs} {φ φ₁ φ₂ : Prop}

theorem entails.rfl : P ⊢ₛ P := entails.refl P

theorem bientails.rfl {P : SPred σs} : P ⊣⊢ₛ P := bientails.refl P
theorem bientails.of_eq {P Q : SPred σs} (h : P = Q) : P ⊣⊢ₛ Q := h ▸ .rfl

theorem bientails.mp {P Q : SPred σs} : (P ⊣⊢ₛ Q) → (P ⊢ₛ Q) := fun h => (bientails.iff.mp h).1
theorem bientails.mpr {P Q : SPred σs} : (P ⊣⊢ₛ Q) → (Q ⊢ₛ P) := fun h => (bientails.iff.mp h).2

/-! # Connectives -/

theorem and_intro_l (h : P ⊢ₛ Q) : P ⊢ₛ Q ∧ P := and_intro h .rfl
theorem and_intro_r (h : P ⊢ₛ Q) : P ⊢ₛ P ∧ Q := and_intro .rfl h
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
theorem exists_intro' {α} {σs} {P} {Ψ : α → SPred σs} (a : α) (h : P ⊢ₛ Ψ a) : P ⊢ₛ ∃ a, Ψ a := h.trans (exists_intro a)
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
  bientails.iff.mpr ⟨or_elim (and_intro or_intro_l or_intro_l) (and_mono or_intro_r or_intro_r),
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

-- Sort-of modus ponens:
theorem and_imp : P' ∧ (P' → Q') ⊢ₛ P' ∧ Q' := and_intro and_elim_l (and_comm.mp.trans (imp_elim .rfl))
theorem of_and_imp (hp : P ⊢ₛ P') (hq : Q ⊢ₛ (P' → Q')) : P ∧ Q ⊢ₛ P' ∧ Q' := (and_mono hp hq).trans and_imp

/-! # Pure -/

theorem pure_elim {φ : Prop} (h1 : Q ⊢ₛ ⌜φ⌝) (h2 : φ → Q ⊢ₛ R) : Q ⊢ₛ R :=
  and_self.mpr.trans <| imp_elim <| h1.trans <| pure_elim' fun h =>
    imp_intro' <| and_elim_l.trans (h2 h)

@[grind ←]
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

@[simp, grind =] theorem true_intro_simp : (Q ⊢ₛ ⌜True⌝) ↔ True := iff_true_intro true_intro

@[simp] theorem _root_.ULift.down_dite {φ : Prop} [Decidable φ] (t : φ → α) (e : ¬φ → α) : (ULift.down (if h : φ then ⟨t h⟩ else ⟨e h⟩)) = if h : φ then t h else e h := apply_dite _ _ _ _
@[simp] theorem _root_.ULift.down_ite {φ : Prop} [Decidable φ] (t e : α) : (ULift.down (if φ then ⟨t⟩ else ⟨e⟩)) = if φ then t else e := apply_ite _ _ _ _

/-! # Miscellaneous -/

theorem and_left_comm : P ∧ Q ∧ R ⊣⊢ₛ Q ∧ P ∧ R := and_assoc.symm.trans <| (and_congr_l and_comm).trans and_assoc
theorem and_right_comm : (P ∧ Q) ∧ R ⊣⊢ₛ (P ∧ R) ∧ Q := and_assoc.trans <| (and_congr_r and_comm).trans and_assoc.symm

/-! # Working with entailment -/

-- NB: We cannot currently make the following lemma @[grind =]; we are blocked on #9623.
theorem entails_pure_elim_cons {σ : Type u} [Inhabited σ] (P Q : Prop) : entails ⌜P⌝ (σs := σ::σs) ⌜Q⌝ ↔ entails ⌜P⌝ (σs := σs) ⌜Q⌝ := by simp [entails]
@[simp] theorem entails_true_intro (P Q : SPred σs) : (⊢ₛ P → Q) = (P ⊢ₛ Q) := propext <| Iff.intro (fun h => (and_intro true_intro .rfl).trans (imp_elim h)) (fun h => imp_intro (and_elim_r.trans h))
-- The following lemmas work around a DefEq incompleteness that would be fixed by #9015.
@[simp] theorem entails_1 {P Q : SPred [σ]} : SPred.entails P Q = (∀ s, (P s).down → (Q s).down) := rfl
@[simp] theorem entails_2 {P Q : SPred [σ₁, σ₂]} : SPred.entails P Q = (∀ s₁ s₂, (P s₁ s₂).down → (Q s₁ s₂).down) := rfl
@[simp] theorem entails_3 {P Q : SPred [σ₁, σ₂, σ₃]} : SPred.entails P Q = (∀ s₁ s₂ s₃, (P s₁ s₂ s₃).down → (Q s₁ s₂ s₃).down) := rfl
@[simp] theorem entails_4 {P Q : SPred [σ₁, σ₂, σ₃, σ₄]} : SPred.entails P Q = (∀ s₁ s₂ s₃ s₄, (P s₁ s₂ s₃ s₄).down → (Q s₁ s₂ s₃ s₄).down) := rfl
@[simp] theorem entails_5 {P Q : SPred [σ₁, σ₂, σ₃, σ₄, σ₅]} : SPred.entails P Q = (∀ s₁ s₂ s₃ s₄ s₅, (P s₁ s₂ s₃ s₄ s₅).down → (Q s₁ s₂ s₃ s₄ s₅).down) := rfl

/-! # Tactic support -/

namespace Tactic

/-- Tautology in `SPred` as a quotable definition. -/
abbrev tautological (Q : SPred σs) : Prop := ⊢ₛ Q

/--
A mapping from propositions to `SPred` tautologies that are known to be logically equivalent.
This is used to rewrite proof goals into a form that is suitable for use with `mvcgen`.
-/
class PropAsSPredTautology (φ : Prop) {σs : outParam (List (Type u))} (P : outParam (SPred σs)) : Prop where
  /-- A proof that `φ` and `P` are logically equivalent. -/
  iff : φ ↔ ⊢ₛ P
instance {φ : SPred []} : PropAsSPredTautology φ.down φ where iff := true_imp_iff.symm
instance : PropAsSPredTautology (P ⊢ₛ Q) spred(P → Q) where iff := iff_of_eq (entails_true_intro P Q).symm
instance : PropAsSPredTautology (⊢ₛ P) P where iff := Iff.rfl

/--
A mapping from `SPred` to pure propositions that are known to be equivalent.
-/
class IsPure (P : SPred σs) (φ : outParam Prop) where
  /--
  A proof that `P` and `φ` are equivalent.
  -/
  to_pure : P ⊣⊢ₛ ⌜φ⌝
instance (σs) : IsPure (σs:=σs) ⌜φ⌝ φ where to_pure := .rfl
instance (σs) : IsPure (σs:=σs) spred(⌜φ⌝ → ⌜ψ⌝) (φ → ψ) where to_pure := pure_imp
instance (σs) : IsPure (σs:=σs) spred(⌜φ⌝ ∧ ⌜ψ⌝) (φ ∧ ψ) where to_pure := pure_and
instance (σs) : IsPure (σs:=σs) spred(⌜φ⌝ ∨ ⌜ψ⌝) (φ ∨ ψ) where to_pure := pure_or
instance (σs) (P : α → Prop) : IsPure (σs:=σs) spred(∃ x, ⌜P x⌝) (∃ x, P x) where to_pure := pure_exists
instance (σs) (P : α → Prop) : IsPure (σs:=σs) spred(∀ x, ⌜P x⌝) (∀ x, P x) where to_pure := pure_forall
instance (σs) (P : SPred (σ::σs)) [inst : IsPure P φ] : IsPure (σs:=σs) spred(P s) φ where to_pure := (iff_of_eq bientails_cons).mp inst.to_pure s
instance (σs) (P : SPred σs) [inst : IsPure P φ] : IsPure (σs:=σ::σs) (fun _ => P) φ where to_pure := (iff_of_eq bientails_cons).mpr (fun _ => inst.to_pure)
instance (φ : Prop) : IsPure (σs:=[]) ⌜φ⌝ φ where to_pure := Iff.rfl
instance (P : SPred []) : IsPure (σs:=[]) P P.down where to_pure := Iff.rfl

/--
A decomposition of a stateful predicate into the conjunction of two other stateful predicates.

Decomposing assertions in postconditions into conjunctions of simpler predicates increases the
chance that automation will be able to prove the entailment of the postcondition and the next precondition.
-/
class IsAnd (P : SPred σs) (Q₁ Q₂ : outParam (SPred σs)) where
  /-- A proof that the decomposition is logically equivalent to the original predicate. -/
  to_and : P ⊣⊢ₛ Q₁ ∧ Q₂
instance (σs) (Q₁ Q₂ : SPred σs) : IsAnd (σs:=σs) spred(Q₁ ∧ Q₂) Q₁ Q₂ where to_and := .rfl
instance (σs) : IsAnd (σs:=σs) ⌜p ∧ q⌝ ⌜p⌝ ⌜q⌝ where to_and := pure_and.symm
instance (σs) (P Q₁ Q₂ : σ → SPred σs) [base : ∀ s, IsAnd (P s) (Q₁ s) (Q₂ s)] : IsAnd (σs:=σ::σs) P Q₁ Q₂ where to_and := fun s => (base s).to_and

theorem ProofMode.start_entails {φ : Prop} [PropAsSPredTautology φ P] : (⊢ₛ P) → φ := PropAsSPredTautology.iff.mpr
theorem ProofMode.elim_entails {φ : Prop} [PropAsSPredTautology φ P] : φ → (⊢ₛ P) := PropAsSPredTautology.iff.mp

theorem Assumption.left {P Q R : SPred σs} (h : P ⊢ₛ R) : P ∧ Q ⊢ₛ R := and_elim_l.trans h
theorem Assumption.right {P Q R : SPred σs} (h : Q ⊢ₛ R) : P ∧ Q ⊢ₛ R := and_elim_r.trans h
theorem Cases.add_goal {σs} {P Q H T : SPred σs} (hand : Q ∧ H ⊣⊢ₛ P) (hgoal : P ⊢ₛ T) : Q ∧ H ⊢ₛ T := hand.mp.trans hgoal
theorem Cases.clear {σs} {Q H T : SPred σs} (hgoal : Q ∧ ⌜True⌝ ⊢ₛ T) : Q ∧ H ⊢ₛ T := (and_mono_r true_intro).trans hgoal
theorem Cases.pure {σs} {Q T : SPred σs} (hgoal : Q ∧ ⌜True⌝ ⊢ₛ T) : Q ⊢ₛ T := (and_intro .rfl true_intro).trans hgoal
theorem Cases.and_1 {σs} {Q H₁' H₂' H₁₂' T : SPred σs} (hand : H₁' ∧ H₂' ⊣⊢ₛ H₁₂') (hgoal : Q ∧ H₁₂' ⊢ₛ T) : (Q ∧ H₁') ∧ H₂' ⊢ₛ T := ((and_congr_r hand.symm).trans and_assoc.symm).mpr.trans hgoal
theorem Cases.and_2 {σs} {Q H₁' H₂ T : SPred σs} (hgoal : (Q ∧ H₁') ∧ H₂ ⊢ₛ T) : (Q ∧ H₂) ∧ H₁' ⊢ₛ T := and_right_comm.mp.trans hgoal
theorem Cases.and_3 {σs} {Q H₁ H₂ H T : SPred σs} (hand : H ⊣⊢ₛ H₁ ∧ H₂) (hgoal : (Q ∧ H₂) ∧ H₁ ⊢ₛ T) : Q ∧ H ⊢ₛ T := (and_congr_r hand).mp.trans (and_assoc.mpr.trans (and_right_comm.mp.trans hgoal))
theorem Cases.exists {Q : SPred σs} {ψ : α → SPred σs} {T : SPred σs} (h : ∀ a, Q ∧ ψ a ⊢ₛ T) : Q ∧ (∃ a, ψ a) ⊢ₛ T := imp_elim' (exists_elim fun a => imp_intro (entails.trans and_symm (h a)))
theorem Clear.clear {P P' A Q : SPred σs} (hfocus : P ⊣⊢ₛ P' ∧ A) (h : P' ⊢ₛ Q) : P ⊢ₛ Q := hfocus.mp.trans <| (and_mono_l h).trans and_elim_l
theorem Exact.assumption {P P' A : SPred σs} (h : P ⊣⊢ₛ P' ∧ A) : P ⊢ₛ A := h.mp.trans and_elim_r
theorem Exact.from_tautology {P T : SPred σs} [PropAsSPredTautology φ T] (h : φ) : P ⊢ₛ T := true_intro.trans (PropAsSPredTautology.iff.mp h)
theorem Focus.this {P : SPred σs} : P ⊣⊢ₛ ⌜True⌝ ∧ P := true_and.symm
theorem Focus.left {P P' Q C R : SPred σs} (h₁ : P ⊣⊢ₛ P' ∧ R) (h₂ : P' ∧ Q ⊣⊢ₛ C) : P ∧ Q ⊣⊢ₛ C ∧ R := (and_congr_l h₁).trans (and_right_comm.trans (and_congr_l h₂))
theorem Focus.right {P Q Q' C R : SPred σs} (h₁ : Q ⊣⊢ₛ Q' ∧ R) (h₂ : P ∧ Q' ⊣⊢ₛ C) : P ∧ Q ⊣⊢ₛ C ∧ R := (and_congr_r h₁).trans (and_assoc.symm.trans (and_congr_l h₂))
theorem Focus.rewrite_hyps {σs} {P Q R : SPred σs} (hrw : P ⊣⊢ₛ Q) (hgoal : Q ⊢ₛ R) : P ⊢ₛ R := hrw.mp.trans hgoal
theorem Have.dup {P Q H T : SPred σs} (hfoc : P ⊣⊢ₛ Q ∧ H) (hgoal : P ∧ H ⊢ₛ T) : P ⊢ₛ T := (and_intro .rfl (hfoc.mp.trans and_elim_r)).trans hgoal
theorem Have.have {P H PH T : SPred σs} (hand : P ∧ H ⊣⊢ₛ PH) (hhave : P ⊢ₛ H) (hgoal : PH ⊢ₛ T) : P ⊢ₛ T := (and_intro .rfl hhave).trans (hand.mp.trans hgoal)
theorem Have.replace {P H H' PH PH' T : SPred σs} (hfoc : PH ⊣⊢ₛ P ∧ H ) (hand : P ∧ H' ⊣⊢ₛ PH') (hhave : PH ⊢ₛ H') (hgoal : PH' ⊢ₛ T) : PH ⊢ₛ T := (and_intro (hfoc.mp.trans and_elim_l) hhave).trans (hand.mp.trans hgoal)
theorem Intro.intro {P Q H T : SPred σs} (hand : Q ∧ H ⊣⊢ₛ P) (h : P ⊢ₛ T) : Q ⊢ₛ H → T := imp_intro (hand.mp.trans h)
theorem Revert.and_pure_intro_r {φ : Prop} {P P' Q : SPred σs} (h₁ : φ) (hand : P ∧ ⌜φ⌝ ⊣⊢ₛ P') (h₂ : P' ⊢ₛ Q) : P ⊢ₛ Q := (SPred.and_intro_r (SPred.pure_intro h₁)).trans (hand.mp.trans h₂)
theorem Pure.thm {P Q T : SPred σs} {φ : Prop} [IsPure Q φ] (h : φ → P ⊢ₛ T) : P ∧ Q ⊢ₛ T := by
  apply pure_elim
  · exact and_elim_r.trans IsPure.to_pure.mp
  · intro hp
    exact and_elim_l.trans (h hp)
/-- A generalization of `pure_intro` exploiting `IsPure`. -/
theorem Pure.intro {P Q : SPred σs} {φ : Prop} [IsPure Q φ] (hφ : φ) : P ⊢ₛ Q := (pure_intro hφ).trans IsPure.to_pure.mpr
theorem Revert.revert {P Q H T : SPred σs} (hfoc : P ⊣⊢ₛ Q ∧ H) (h : Q ⊢ₛ H → T) : P ⊢ₛ T := hfoc.mp.trans (imp_elim h)
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

theorem Specialize.forall {α} {σs} {ψ : α → SPred σs} {P : SPred σs} (a : α) : P ∧ (∀ x, ψ x) ⊢ₛ P ∧ ψ a := and_mono_r (forall_elim a)
theorem Specialize.pure_start {φ : Prop} {H P T : SPred σs} [PropAsSPredTautology φ H] (hpure : φ) (hgoal : P ∧ H ⊢ₛ T) : P ⊢ₛ T := (and_intro .rfl (true_intro.trans (PropAsSPredTautology.iff.mp hpure))).trans hgoal
theorem Specialize.pure_taut {σs} {φ} {P : SPred σs} [IsPure P φ] (h : φ) : ⊢ₛ P := (pure_intro h).trans IsPure.to_pure.mpr
theorem Specialize.focus {P P' Q R : SPred σs} (hfocus : P ⊣⊢ₛ P' ∧ Q) (hnew : P' ∧ Q ⊢ₛ R) : P ⊢ₛ R := hfocus.mp.trans hnew

/--
Expresses that the conjunction of `P` and `Q` is equivalent to `spred(P ∧ Q)`, but potentially
simpler.
-/
class SimpAnd (P Q : SPred σs) (PQ : outParam (SPred σs)) : Prop where
  /-- A proof that `spred(P ∧ Q)` is logically equivalent to `PQ`.-/
  simp_and : P ∧ Q ⊣⊢ₛ PQ
instance (σs) (P Q : SPred σs) : SimpAnd P Q (spred(P ∧ Q)) where simp_and := .rfl
instance (σs) (P : SPred σs) : SimpAnd P ⌜True⌝ P where simp_and := and_true
instance (σs) (P : SPred σs) : SimpAnd ⌜True⌝ P P where simp_and := true_and

/--
Provides a decomposition of a stateful predicate (`P`) into stateful and pure components (`P'` and
`φ`, respectively).
-/
class HasFrame (P : SPred σs) (P' : outParam (SPred σs)) (φ : outParam Prop) : Prop where
  /--
  A proof that the original stateful predicate is equivalent to the decomposed form.
  -/
  reassoc : P ⊣⊢ₛ P' ∧ ⌜φ⌝
instance (σs) (P P' Q QP : SPred σs) [HasFrame P Q φ] [SimpAnd Q P' QP]: HasFrame (σs:=σs) spred(P ∧ P') QP φ where reassoc := ((and_congr_l HasFrame.reassoc).trans and_right_comm).trans (and_congr_l SimpAnd.simp_and)
instance (σs) (P P' Q' PQ : SPred σs) [HasFrame P' Q' φ] [SimpAnd P Q' PQ]: HasFrame (σs:=σs) spred(P ∧ P') PQ φ where reassoc := ((and_congr_r HasFrame.reassoc).trans and_assoc.symm).trans (and_congr_l SimpAnd.simp_and)
instance (σs) (P P' : Prop) (Q : SPred σs) [HasFrame spred(⌜P⌝ ∧ ⌜P'⌝) Q φ] : HasFrame (σs:=σs) ⌜P ∧ P'⌝ Q φ where reassoc := pure_and.symm.trans HasFrame.reassoc
instance (σs) (P P' : SVal.StateTuple σs → Prop) (Q : SPred σs) [HasFrame spred(SVal.curry (fun t => ⟨P t⟩) ∧ SVal.curry (fun t => ⟨P' t⟩)) Q φ] : HasFrame (σs:=σs) (SVal.curry fun t => ⟨P t ∧ P' t⟩) Q φ where reassoc := and_curry.symm.trans HasFrame.reassoc
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
instance (σs) : HasFrame (σs:=σs) ⌜φ⌝ ⌜True⌝ φ where reassoc := true_and.symm
instance {P : SPred []} : HasFrame (σs:=[]) P ⌜True⌝ P.down where reassoc := true_and.symm

theorem Frame.frame {P Q T : SPred σs} {φ : Prop} [HasFrame P Q φ]
  (h : φ → Q ⊢ₛ T) : P ⊢ₛ T := by
    apply SPred.pure_elim
    · exact HasFrame.reassoc.mp.trans SPred.and_elim_r
    · intro hp
      exact HasFrame.reassoc.mp.trans (SPred.and_elim_l' (h hp))
