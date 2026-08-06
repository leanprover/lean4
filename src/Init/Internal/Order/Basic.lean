/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joachim Breitner
-/
module

prelude

public import Init.System.IO  -- for `MonoBind` instance
import all Init.Control.Except  -- for `MonoBind` instance
import all Init.Control.StateRef  -- for `MonoBind` instance
import all Init.Control.Option  -- for `MonoBind` instance
import all Init.System.ST  -- for `MonoBind` instance
import Init.ByCases

public section

/-!
This module contains some basic definitions and results from domain theory, intended to be used as
the underlying construction of the `partial_fixpoint` feature. It is not meant to be used as a
general purpose library for domain theory, but can be of interest to users who want to extend
the `partial_fixpoint` machinery (e.g. mark more functions as monotone or register more monads).

This follows the corresponding
[Isabelle development](https://isabelle.in.tum.de/library/HOL/HOL/Partial_Function.html), as also
described in [Alexander Krauss: Recursive Deﬁnitions of Monadic Functions](https://www21.in.tum.de/~krauss/papers/mrec.pdf).
-/

universe u v w

namespace Lean.Order

/--
A partial order is a reflexive, transitive and antisymmetric relation.

This is intended to be used in the construction of `partial_fixpoint`, and not meant to be used otherwise.
-/
class PartialOrder (α : Sort u) where
  /--
  A “less-or-equal-to” or “approximates” relation.

  This is intended to be used in the construction of `partial_fixpoint`, and not meant to be used otherwise.
  -/
  rel : α → α → Prop
  /-- The “less-or-equal-to” or “approximates” relation is reflexive. -/
  rel_refl : ∀ {x}, rel x x
  /-- The “less-or-equal-to” or “approximates” relation is transitive. -/
  rel_trans : ∀ {x y z}, rel x y → rel y z → rel x z
  /-- The “less-or-equal-to” or “approximates” relation is antisymmetric. -/
  rel_antisymm : ∀ {x y}, rel x y → rel y x → x = y

@[inherit_doc] scoped infix:50 " ⊑ " => PartialOrder.rel

attribute [grind .] PartialOrder.rel_refl

section PartialOrder

variable {α  : Sort u} [PartialOrder α]

theorem PartialOrder.rel_of_eq {x y : α} (h : x = y) : x ⊑ y := by cases h; apply rel_refl

/--
A chain is a totally ordered set (representing a set as a predicate).

This is intended to be used in the construction of `partial_fixpoint`, and not meant to be used otherwise.
-/
@[expose] def chain (c : α → Prop) : Prop := ∀ x y , c x → c y → x ⊑ y ∨ y ⊑ x

@[expose] def is_sup {α : Sort u} [PartialOrder α] (c : α → Prop) (s : α) : Prop :=
  ∀ x, s ⊑ x ↔ (∀ y, c y → y ⊑ x)

theorem is_sup_unique {α} [PartialOrder α] {c : α → Prop} {s₁ s₂ : α}
    (h₁ : is_sup c s₁) (h₂ : is_sup c s₂) : s₁ = s₂ := by
  apply PartialOrder.rel_antisymm
  · apply (h₁ s₂).mpr
    intro y hy
    apply (h₂ s₂).mp PartialOrder.rel_refl y hy
  · apply (h₂ s₁).mpr
    intro y hy
    apply (h₁ s₁).mp PartialOrder.rel_refl y hy

end PartialOrder

section CCPO

open PartialOrder

/--
A chain-complete partial order (CCPO) is a partial order where every chain has a least upper bound.

This is intended to be used in the construction of `partial_fixpoint`, and not meant to be used
otherwise.
-/
class CCPO (α : Sort u) extends PartialOrder α where
  /--
  The least upper bound of chains exists.
  -/
  has_csup {c : α → Prop} (hc : chain c) : Exists (is_sup c)

open  CCPO

variable {α  : Sort u} [CCPO α]

noncomputable def CCPO.csup {c : α → Prop} (hc : chain c) : α :=
  Classical.choose (CCPO.has_csup hc)

theorem CCPO.csup_spec {c : α → Prop} (hc : chain c) : is_sup c (csup hc) :=
  @fun x => Classical.choose_spec (CCPO.has_csup hc) x

theorem csup_le {c : α → Prop} (hc : chain c) : (∀ y, c y → y ⊑ x) → csup hc ⊑ x :=
  (csup_spec hc x).mpr

theorem le_csup {c : α → Prop} (hc : chain c) {y : α} (hy : c y) : y ⊑ csup hc :=
  (csup_spec hc (csup hc)).mp rel_refl y hy

def empty_chain (α) : α → Prop := fun _ => False

theorem chain_empty (α : Sort u) [PartialOrder α] : chain (empty_chain α) := by
  intro x y hx hy; contradiction

/--
The bottom element is the least upper bound of the empty chain.

This is intended to be used in the construction of `partial_fixpoint`, and not meant to be used otherwise.
-/
noncomputable def bot : α := csup (chain_empty α)

scoped notation "⊥" => bot

theorem bot_le (x : α) : ⊥ ⊑ x := by
  apply csup_le
  intro x y; contradiction

end CCPO


section CompleteLattice

/--
A complete lattice is a partial order where every subset has a least upper bound.
-/
class CompleteLattice (α : Sort u) extends PartialOrder α where
  /--
  The least upper bound of an arbitrary subset exists.
  -/
  has_sup (c : α → Prop) : Exists (is_sup c)

open PartialOrder CompleteLattice

variable {α  : Sort u} [CompleteLattice α]

noncomputable def CompleteLattice.sup (c : α → Prop) : α :=
  Classical.choose (CompleteLattice.has_sup c)

theorem CompleteLattice.sup_spec (c : α → Prop) : is_sup c (sup c) :=
  @fun x => Classical.choose_spec (CompleteLattice.has_sup c) x

theorem sup_le (c : α → Prop) : (∀ y, c y → y ⊑ x) → sup c ⊑ x :=
  Iff.mpr (sup_spec c x)

theorem le_sup (c : α → Prop) {y : α} (hy : c y) : y ⊑ sup c :=
  Iff.mp (sup_spec c (sup c)) rel_refl y hy

noncomputable def inf (c : α → Prop) : α := sup (∀ y, c y → · ⊑ y)

theorem inf_spec {c : α → Prop} : x ⊑ inf c ↔ (∀ y, c y → x ⊑ y) where
  mp := by
    unfold inf
    intro h
    intro y cy
    suffices g : (sup fun x => ∀ (y : α), c y → x ⊑ y) ⊑ y from
      by
        apply rel_trans h g
    apply sup_le
    intro z
    intro i
    exact i y cy
  mpr := by
    unfold inf
    intro h
    apply le_sup
    apply h

theorem le_inf {c : α → Prop} : (∀ y, c y → x ⊑ y) → x ⊑ inf c := inf_spec.mpr

theorem inf_le  {c : α → Prop} {y : α} (hy : c y) : inf c ⊑ y := inf_spec.mp (rel_refl) y hy

end CompleteLattice

section monotone

variable {α : Sort u} [PartialOrder α]
variable {β : Sort v} [PartialOrder β]

/--
A function is monotone if it maps related elements to related elements.

This is intended to be used in the construction of `partial_fixpoint`, and not meant to be used otherwise.
-/
@[expose] def monotone (f : α → β) : Prop := ∀ x y, x ⊑ y → f x ⊑ f y

theorem monotone_const (c : β) : monotone (fun (_ : α) => c) :=
  fun _ _ _ => PartialOrder.rel_refl

theorem monotone_id : monotone (fun (x : α) => x) :=
  fun _ _ hxy => hxy

theorem monotone_compose
    {γ : Sort w} [PartialOrder γ]
    {f : α → β} {g : β → γ}
    (hf : monotone f) (hg : monotone g) :
   monotone (fun x => g (f x)) := fun _ _ hxy => hg _ _ (hf _ _ hxy)

end monotone

section admissibility

variable {α : Sort u} [CCPO α]

open PartialOrder CCPO

/--
A predicate is admissible if it can be transferred from the elements of a chain to the chains least
upper bound. Such predicates can be used in fixpoint induction.

This definition implies `P ⊥`. Sometimes (e.g. in Isabelle) the empty chain is excluded
from this definition, and `P ⊥` is a separate condition of the induction predicate.

This is intended to be used in the construction of `partial_fixpoint`, and not meant to be used otherwise.
-/
def admissible (P : α → Prop) :=
  ∀ (c : α → Prop) (hc : chain c), (∀ x, c x → P x) → P (csup hc)

theorem admissible_const_true : admissible (fun (_ : α) => True) :=
  fun _ _ _ => trivial

theorem admissible_and (P Q : α → Prop)
  (hadm₁ : admissible P) (hadm₂ : admissible Q) : admissible (fun x => P x ∧ Q x) :=
    fun c hchain h =>
    ⟨ hadm₁ c hchain fun x hx => (h x hx).1,
      hadm₂ c hchain fun x hx => (h x hx).2⟩

theorem chain_conj (c P : α → Prop) (hchain : chain c) : chain (fun x => c x ∧ P x) := by
  intro x y ⟨hcx, _⟩ ⟨hcy, _⟩
  exact hchain x y hcx hcy

theorem csup_conj (c P : α → Prop) (hchain : chain c) (h : ∀ x, c x → ∃ y, c y ∧ x ⊑ y ∧ P y) :
    csup hchain = csup (chain_conj c P hchain) := by
  apply rel_antisymm
  · apply csup_le hchain
    intro x hcx
    obtain ⟨y, hcy, hxy, hPy⟩ := h x hcx
    apply rel_trans hxy; clear x hcx hxy
    apply le_csup (chain_conj _ _ hchain) ⟨hcy, hPy⟩
  · apply csup_le (chain_conj _ _ hchain)
    intro x ⟨hcx, hPx⟩
    apply le_csup hchain hcx

theorem admissible_or (P Q : α → Prop)
  (hadm₁ : admissible P) (hadm₂ : admissible Q) : admissible (fun x => P x ∨ Q x) := by
  intro c hchain h
  have : (∀ x, c x → ∃ y, c y ∧ x ⊑ y ∧ P y) ∨ (∀ x, c x → ∃ y, c y ∧ x ⊑ y ∧ Q y) := by
    open Classical in
    apply Decidable.or_iff_not_imp_left.mpr
    intro h'
    simp only [not_forall, not_exists, not_and] at h'
    obtain ⟨x, hcx, hx⟩ := h'
    intro y hcy
    cases hchain x y hcx hcy  with
    | inl hxy =>
      refine ⟨y, hcy, rel_refl, ?_⟩
      cases h y hcy with
      | inl hPy => exfalso; apply hx y hcy hxy hPy
      | inr hQy => assumption
    | inr hyx =>
      refine ⟨x, hcx, hyx , ?_⟩
      cases h x hcx with
      | inl hPx => exfalso; apply hx x hcx rel_refl hPx
      | inr hQx => assumption
  cases this with
  | inl hP =>
    left
    rw [csup_conj (h := hP) (hchain := hchain)]
    apply hadm₁ _ (chain_conj _ _ hchain)
    intro x ⟨hcx, hPx⟩
    exact hPx
  | inr hQ =>
    right
    rw [csup_conj (h := hQ) (hchain := hchain)]
    apply hadm₂ _ (chain_conj _ _ hchain)
    intro x ⟨hcx, hQx⟩
    exact hQx

theorem admissible_pi (P : α → β → Prop)
  (hadm₁ : ∀ y, admissible (fun x => P x y)) : admissible (fun x => ∀ y, P x y) :=
    fun c hchain h y => hadm₁ y c hchain fun x hx => h x hx y

end admissibility

section lattice_fix
open PartialOrder CompleteLattice

variable {α  : Sort u} [CompleteLattice α]

variable {c : α → Prop}
-- Note that monotonicity is not required for the definition of `lfp`
-- but it is required to show that `lfp` is a fixpoint of `f`.

noncomputable def lfp (f : α → α) : α :=
  inf (fun c => f c ⊑ c)

set_option linter.unusedVariables false in
-- The following definition takes a witness that a function is monotone
noncomputable def lfp_monotone (f : α → α) (hm : monotone f) : α :=
  lfp f

-- Showing that `lfp` is a prefixed point makes use of monotonicity
theorem lfp_prefixed {f : α → α} {hm : monotone f} :
  f (lfp f) ⊑ (lfp f) := by
    apply le_inf
    intro y hy
    suffices h : f (lfp f) ⊑ f y from by
      apply rel_trans h hy
    apply hm
    apply inf_le
    exact hy

-- So does showing that `lfp` is a postfixed point
theorem lfp_postfixed {f : α → α} {hm : monotone f} : lfp f ⊑ f (lfp f) := by
  apply inf_le
  apply hm
  apply lfp_prefixed
  exact hm

-- `lfp` being a fixpoint now follows as an easy corollary
theorem lfp_fix {f : α → α} (hm : monotone f) :
  lfp f = f (lfp f) := by
  apply rel_antisymm
  . apply lfp_postfixed
    exact hm
  . apply lfp_prefixed
    exact hm

-- Same as above, but uses the version of `lfp` that takes a witness of monotonicity
theorem lfp_monotone_fix {f : α → α} {hm : monotone f} :
  lfp_monotone f hm = f (lfp_monotone f hm) := lfp_fix hm

/--
Park induction principle for least fixpoint.
In general, this construction does not require monotonicity of `f`.
Monotonicity is required to show that `lfp f` is indeed a fixpoint of `f`.
-/
theorem lfp_le_of_le {f : α → α} :
  f x ⊑ x → lfp f ⊑ x := fun hx => inf_le hx

/--
Park induction for least fixpoint of a monotone function `f`.
Takes an explicit witness of `f` being monotone.
-/
theorem lfp_le_of_le_monotone (f : α → α) {hm : monotone f} (x : α):
  f x ⊑ x → lfp_monotone f hm ⊑ x := by
    unfold lfp_monotone
    apply lfp_le_of_le

end lattice_fix

section fix

open PartialOrder CCPO

variable {α  : Sort u} [CCPO α]

variable {c : α → Prop} (hchain : chain c)

/--
The transfinite iteration of a function `f` is a set that is `⊥ ` and is closed under application
of `f` and `csup`.

This is intended to be used in the construction of `partial_fixpoint`, and not meant to be used otherwise.
-/
inductive iterates (f : α → α) : α → Prop where
  | step : iterates f x → iterates f (f x)
  | sup {c : α → Prop} (hc : chain c) (hi : ∀ x, c x → iterates f x) : iterates f (csup hc)

theorem chain_iterates {f : α → α} (hf : monotone f) : chain (iterates f) := by
  intro x y hx hy
  induction hx generalizing y
  case step x hx ih =>
    induction hy
    case step y hy _ =>
      cases ih y hy
      · left; apply hf; assumption
      · right; apply hf; assumption
    case sup c hchain hi ih2 =>
      change f x ⊑ csup hchain ∨ csup hchain ⊑ f x
      by_cases h : ∃ z, c z ∧ f x ⊑ z
      · left
        obtain ⟨z, hz, hfz⟩ := h
        apply rel_trans hfz
        apply le_csup hchain hz
      · right
        apply csup_le hchain _
        intro z hz
        rw [not_exists] at h
        specialize h z
        rw [not_and] at h
        specialize h hz
        cases ih2 z hz
        next => contradiction
        next => assumption
  case sup c hchain hi ih =>
    change rel (csup hchain) y ∨ rel y (csup hchain)
    by_cases h : ∃ z, c z ∧ rel y z
    · right
      obtain ⟨z, hz, hfz⟩ := h
      apply rel_trans hfz
      apply le_csup hchain hz
    · left
      apply csup_le hchain _
      intro z hz
      rw [not_exists] at h
      specialize h z
      rw [not_and] at h
      specialize h hz
      cases ih z hz y hy
      next => assumption
      next => contradiction

theorem rel_f_of_iterates {f : α → α} (hf : monotone f) {x : α} (hx : iterates f x) : x ⊑ f x := by
  induction hx
  case step ih =>
    apply hf
    assumption
  case sup c hchain hi ih =>
    apply csup_le hchain
    intro y hy
    apply rel_trans (ih y hy)
    apply hf
    apply le_csup hchain hy

set_option linter.unusedVariables false in
/--
The least fixpoint of a monotone function is the least upper bound of its transfinite iteration.

The `monotone f` assumption is not strictly necessarily for the definition, but without this the
definition is not very meaningful and it simplifies applying theorems like `fix_eq` if every use of
`fix` already has the monotonicity requirement.

This is intended to be used in the construction of `partial_fixpoint`, and not meant to be used otherwise.
-/
noncomputable def fix (f : α → α) (hmono : monotone f) := csup (chain_iterates hmono)

/--
The main fixpoint theorem for fixed points of monotone functions in chain-complete partial orders.

This is intended to be used in the construction of `partial_fixpoint`, and not meant to be used otherwise.
-/
theorem fix_eq {f : α → α} (hf : monotone f) : fix f hf = f (fix f hf) := by
  apply rel_antisymm
  · apply rel_f_of_iterates hf
    apply iterates.sup (chain_iterates hf)
    exact fun _ h => h
  · apply le_csup (chain_iterates hf)
    apply iterates.step
    apply iterates.sup (chain_iterates hf)
    intro y hy
    exact hy

/--
The fixpoint induction theme: An admissible predicate holds for a least fixpoint if it is preserved
by the fixpoint's function.

This is intended to be used in the construction of `partial_fixpoint`, and not meant to be used otherwise.
-/
theorem fix_induct {f : α → α} (hf : monotone f)
    (motive : α → Prop) (hadm: admissible motive)
    (h : ∀ x, motive x → motive (f x)) : motive (fix f hf) := by
  apply hadm _ (chain_iterates hf)
  intro x hiterates
  induction hiterates with
  | @step x hiter ih => apply h x ih
  | @sup c hchain hiter ih => apply hadm c hchain ih

end fix

section fun_order

open PartialOrder

variable {α : Sort u}
variable {β : α → Sort v}
variable {γ : Sort w}

instance instOrderPi [∀ x, PartialOrder (β x)] : PartialOrder (∀ x, β x) where
  rel f g := ∀ x, f x ⊑ g x
  rel_refl _ := rel_refl
  rel_trans hf hg x := rel_trans (hf x) (hg x)
  rel_antisymm hf hg := funext (fun x => rel_antisymm (hf x) (hg x))

theorem monotone_of_monotone_apply [PartialOrder γ] [∀ x, PartialOrder (β x)] (f : γ → (∀ x, β x))
  (h : ∀ y, monotone (fun x => f x y)) : monotone f :=
  fun x y hxy z => h z x y hxy

theorem monotone_apply [PartialOrder γ] [∀ x, PartialOrder (β x)] (a : α) (f : γ → ∀ x, β x)
    (h : monotone f) :
    monotone (fun x => f x a) := fun _ _ hfg => h _ _ hfg a

theorem chain_apply [∀ x, PartialOrder (β x)] {c : (∀ x, β x) → Prop} (hc : chain c) (x : α) :
    chain (fun y => ∃ f, c f ∧ f x = y) := by
  intro _ _ ⟨f, hf, hfeq⟩ ⟨g, hg, hgeq⟩
  subst hfeq; subst hgeq
  cases hc f g hf hg
  next h => left; apply h x
  next h => right; apply h x

noncomputable def fun_csup [∀ x, CCPO (β x)] (c : (∀ x, β x) → Prop) (hc : chain c) (x : α) :=
  CCPO.csup (chain_apply hc x)

theorem fun_csup_is_sup [∀ x, CCPO (β x)] (c : (∀ x, β x) → Prop) (hc : chain c) :
    is_sup c (fun_csup c hc) := by
  intro f
  constructor
  next =>
    intro hf g hg x
    apply rel_trans _ (hf x); clear hf
    apply le_csup (chain_apply hc x)
    exact ⟨g, hg, rfl⟩
  next =>
    intro h x
    apply csup_le (chain_apply hc x)
    intro y ⟨z, hz, hyz⟩
    subst y
    apply h z hz

instance instCCPOPi [∀ x, CCPO (β x)] : CCPO (∀ x, β x) where
  has_csup hc := ⟨fun_csup _ hc, fun_csup_is_sup _ hc⟩

theorem fun_csup_eq [∀ x, CCPO (β x)] (c : (∀ x, β x) → Prop) (hc : chain c) :
    fun_csup c hc = CCPO.csup hc := by
  apply is_sup_unique (c := c)
  · apply fun_csup_is_sup
  · apply CCPO.csup_spec

noncomputable def fun_sup [∀ x, CompleteLattice (β x)] (c : (∀ x, β x) → Prop) (x : α) :=
  CompleteLattice.sup (fun y => ∃ f, c f ∧ f x = y)

theorem fun_sup_is_sup [∀ x, CompleteLattice (β x)] (c : (∀ x, β x) → Prop) :
    is_sup c (fun_sup c) := by
  intro f
  constructor
  case mp =>
    intro hf g hg x
    apply rel_trans _ (hf x)
    apply le_sup
    exact ⟨g, hg, rfl⟩
  case mpr =>
    intro h x
    apply sup_le
    intro y ⟨z, hz, hyz⟩
    subst y
    apply h z hz

instance instCompleteLatticePi [∀ x, CompleteLattice (β x)] : CompleteLattice (∀ x, β x) where
  has_sup c := ⟨fun_sup c, fun_sup_is_sup c⟩

theorem fun_sup_eq [∀ x, CompleteLattice (β x)] (c : (∀ x, β x) → Prop) :
    fun_sup c = CompleteLattice.sup c := by
  apply is_sup_unique (c := c)
  · apply fun_sup_is_sup
  · apply CompleteLattice.sup_spec

theorem admissible_apply [∀ x, CCPO (β x)] (P : ∀ x, β x → Prop) (x : α)
  (hadm : admissible (P x)) : admissible (fun (f : ∀ x, β x) => P x (f x)) := by
  intro c hchain h
  rw [← fun_csup_eq]
  apply hadm _ (chain_apply hchain x)
  rintro _ ⟨f, hcf, rfl⟩
  apply h _ hcf

theorem admissible_pi_apply [∀ x, CCPO (β x)] (P : ∀ x, β x → Prop) (hadm : ∀ x, admissible (P x)) :
    admissible (fun (f : ∀ x, β x) => ∀ x, P x (f x)) := by
  apply admissible_pi
  intro
  apply admissible_apply
  apply hadm

end fun_order

section monotone_lemmas

@[partial_fixpoint_monotone]
theorem monotone_ite
    {α : Sort u} {β : Sort v} [PartialOrder α] [PartialOrder β]
    (c : Prop) [Decidable c]
    (k₁ : α → β) (k₂ : α → β)
    (hmono₁ : monotone k₁) (hmono₂ : monotone k₂) :
  monotone fun x => if c then k₁ x else k₂ x := by
    split
    · apply hmono₁
    · apply hmono₂

@[partial_fixpoint_monotone]
theorem monotone_dite
    {α : Sort u} {β : Sort v} [PartialOrder α] [PartialOrder β]
    (c : Prop) [Decidable c]
    (k₁ : α → c → β) (k₂ : α → ¬ c → β)
    (hmono₁ : monotone k₁) (hmono₂ : monotone k₂) :
  monotone fun x => dite c (k₁ x) (k₂ x) := by
    split
    · apply monotone_apply _ _ hmono₁
    · apply monotone_apply _ _ hmono₂
end monotone_lemmas

section pprod_order

open PartialOrder

variable {α : Sort u}
variable {β : Sort v}
variable {γ : Sort w}

instance [PartialOrder α] [PartialOrder β] : PartialOrder (α ×' β) where
  rel a b := a.1 ⊑ b.1 ∧ a.2 ⊑ b.2
  rel_refl := ⟨rel_refl, rel_refl⟩
  rel_trans ha hb := ⟨rel_trans ha.1 hb.1, rel_trans ha.2 hb.2⟩
  rel_antisymm := fun {a} {b} ha hb => by
    cases a; cases b;
    dsimp at *
    rw [rel_antisymm ha.1 hb.1, rel_antisymm ha.2 hb.2]

@[partial_fixpoint_monotone]
theorem PProd.monotone_mk [PartialOrder α] [PartialOrder β] [PartialOrder γ]
    {f : γ → α} {g : γ → β} (hf : monotone f) (hg : monotone g) :
    monotone (fun x => PProd.mk (f x) (g x)) :=
  fun _ _ h12 => ⟨hf _ _ h12, hg _ _ h12⟩

@[partial_fixpoint_monotone]
theorem PProd.monotone_fst [PartialOrder α] [PartialOrder β] [PartialOrder γ]
    {f : γ → α ×' β} (hf : monotone f) : monotone (fun x => (f x).1) :=
  fun _ _ h12 => (hf _ _ h12).1

@[partial_fixpoint_monotone]
theorem PProd.monotone_snd [PartialOrder α] [PartialOrder β] [PartialOrder γ]
    {f : γ → α ×' β} (hf : monotone f) : monotone (fun x => (f x).2) :=
  fun _ _ h12 => (hf _ _ h12).2

def PProd.chain.fst [CCPO α] [CCPO β] (c : α ×' β → Prop) : α → Prop := fun a => ∃ b, c ⟨a, b⟩
def PProd.chain.snd [CCPO α] [CCPO β] (c : α ×' β → Prop) : β → Prop := fun b => ∃ a, c ⟨a, b⟩

def PProd.fst [CompleteLattice α] [CompleteLattice β] (c : α ×' β → Prop) : α → Prop := fun a => ∃ b, c ⟨a, b⟩
def PProd.snd [CompleteLattice α] [CompleteLattice β] (c : α ×' β → Prop) : β → Prop := fun b => ∃ a, c ⟨a, b⟩

theorem PProd.chain.chain_fst [CCPO α] [CCPO β] {c : α ×' β → Prop} (hchain : chain c) :
    chain (chain.fst c) := by
  intro a₁ a₂ ⟨b₁, h₁⟩ ⟨b₂, h₂⟩
  cases hchain ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ h₁ h₂
  case inl h => left; exact h.1
  case inr h => right; exact h.1

theorem PProd.chain.chain_snd [CCPO α] [CCPO β] {c : α ×' β → Prop} (hchain : chain c) :
    chain (chain.snd c) := by
  intro b₁ b₂ ⟨a₁, h₁⟩ ⟨a₂, h₂⟩
  cases hchain ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ h₁ h₂
  case inl h => left; exact h.2
  case inr h => right; exact h.2

noncomputable def prod_csup [CCPO α] [CCPO β] (c : α ×' β → Prop) (hchain : chain c) : α ×' β :=
  ⟨CCPO.csup (PProd.chain.chain_fst hchain), CCPO.csup (PProd.chain.chain_snd hchain)⟩

theorem prod_csup_is_sup [CCPO α] [CCPO β] (c : α ×' β → Prop) (hchain : chain c) :
    is_sup c (prod_csup c hchain) := by
  intro ⟨a, b⟩
  constructor
  next =>
    intro ⟨h₁, h₂⟩ ⟨a', b'⟩ cab
    constructor <;> dsimp at *
    · apply rel_trans ?_ h₁
      apply le_csup (PProd.chain.chain_fst hchain)
      exact ⟨b', cab⟩
    · apply rel_trans ?_ h₂
      apply le_csup (PProd.chain.chain_snd hchain)
      exact ⟨a', cab⟩
  next =>
    intro h
    constructor <;> dsimp
    · apply csup_le (PProd.chain.chain_fst hchain)
      intro a' ⟨b', hcab⟩
      apply (h _ hcab).1
    · apply csup_le (PProd.chain.chain_snd hchain)
      intro b' ⟨a', hcab⟩
      apply (h _ hcab).2

instance instCCPOPProd [CCPO α] [CCPO β] : CCPO (α ×' β) where
  has_csup hchain := ⟨prod_csup _ hchain, prod_csup_is_sup _ hchain⟩

theorem prod_csup_eq [CCPO α] [CCPO β] (c : α ×' β → Prop) (hchain : chain c) :
    prod_csup c hchain = CCPO.csup hchain := by
  apply is_sup_unique (c := c)
  · apply prod_csup_is_sup
  · apply CCPO.csup_spec

noncomputable def prod_sup [CompleteLattice α] [CompleteLattice β] (c : α ×' β → Prop) : α ×' β :=
  ⟨CompleteLattice.sup (PProd.fst c), CompleteLattice.sup (PProd.snd c)⟩

theorem prod_sup_is_sup [CompleteLattice α] [CompleteLattice β] (c : α ×' β → Prop) :
    is_sup c (prod_sup c) := by
  intro ⟨a, b⟩
  constructor
  case mp =>
    intro ⟨h₁, h₂⟩ ⟨a', b'⟩ cab
    constructor <;> dsimp only at *
    · apply rel_trans ?_ h₁
      unfold prod_sup PProd.fst at *
      apply le_sup
      apply Exists.intro b'
      exact cab
    . apply rel_trans ?_ h₂
      apply le_sup
      unfold PProd.snd at *
      apply Exists.intro a'
      exact cab
  case mpr =>
    intro h
    constructor <;> dsimp only
    . apply sup_le
      unfold PProd.fst
      intro y' ex
      apply Exists.elim ex
      intro b' hc
      apply (h ⟨y', b' ⟩ hc).1
    . apply sup_le
      unfold PProd.snd
      intro b' ex
      apply Exists.elim ex
      intro y' hc
      apply (h ⟨y', b' ⟩ hc).2

instance instCompleteLatticePProd [CompleteLattice α] [CompleteLattice β] : CompleteLattice (α ×' β) where
  has_sup c := ⟨prod_sup c, prod_sup_is_sup c⟩

theorem admissible_pprod_fst {α : Sort u} {β : Sort v} [CCPO α] [CCPO β] (P : α → Prop)
    (hadm : admissible P) : admissible (fun (x : α ×' β) => P x.1) := by
  intro c hchain h
  rw [<- prod_csup_eq]
  apply hadm _ (PProd.chain.chain_fst hchain)
  intro x ⟨y, hxy⟩
  apply h ⟨x,y⟩ hxy

theorem admissible_pprod_snd {α : Sort u} {β : Sort v} [CCPO α] [CCPO β] (P : β → Prop)
    (hadm : admissible P) : admissible (fun (x : α ×' β) => P x.2) := by
  intro c hchain h
  rw [<- prod_csup_eq]
  apply hadm _ (PProd.chain.chain_snd hchain)
  intro y ⟨x, hxy⟩
  apply h ⟨x,y⟩ hxy

end pprod_order

section flat_order

variable {α : Sort u}

set_option linter.unusedVariables false in
/--
`FlatOrder b` wraps the type `α` with the flat partial order generated by `∀ x, b ⊑ x`.

This is intended to be used in the construction of `partial_fixpoint`, and not meant to be used otherwise.
-/
@[expose] def FlatOrder {α : Sort u} (b : α) := α

def FlatOrder.mk {α : Sort u} (b : α) (x : α) : FlatOrder b := x

def FlatOrder.inner {α : Sort u} {b : α} (x : FlatOrder b) : α := x

theorem FlatOrder.mk_inner {α : Sort u} {b : α} {x : FlatOrder b} :
    FlatOrder.mk b x.inner = x :=
  (rfl)

theorem FlatOrder.inner_mk {α : Sort u} {b : α} {x : α} :
    (FlatOrder.mk b x).inner = x :=
  (rfl)

@[simp]
theorem FlatOrder.mk_inj {α : Sort u} {b : α} {x y : α} :
    FlatOrder.mk b x = FlatOrder.mk b y ↔ x = y :=
  Iff.rfl

variable {b : α}

/--
The flat partial order generated by `∀ x, b ⊑ x`.

This is intended to be used in the construction of `partial_fixpoint`, and not meant to be used otherwise.
-/
inductive FlatOrder.rel : (x y : FlatOrder b) → Prop where
  | bot : rel b x
  | refl : rel x x

instance FlatOrder.instOrder : PartialOrder (FlatOrder b) where
  rel := rel
  rel_refl := .refl
  rel_trans {x y z : α} (hxy : rel x y) (hyz : rel y z) := by
    cases hxy <;> cases hyz <;> constructor
  rel_antisymm {x y : α} (hxy : rel x y) (hyz : rel y x) : x = y := by
    cases hxy <;> cases hyz <;> constructor

open Classical in
private theorem Classical.some_spec₂ {α : Sort _} {p : α → Prop} {h : ∃ a, p a} (q : α → Prop)
    (hpq : ∀ a, p a → q a) : q (choose h) := hpq _ <| choose_spec _

noncomputable def flat_csup (c : FlatOrder b → Prop) : FlatOrder b := by
  by_cases h : ∃ (x : FlatOrder b), c x ∧ x ≠ b
  · exact Classical.choose h
  · exact .mk b b

theorem flat_csup_is_sup (c : FlatOrder b → Prop) (hc : chain c) :
    is_sup c (flat_csup c) := by
  intro x
  unfold flat_csup
  split
  next hex =>
    apply Classical.some_spec₂ (q := (· ⊑ x ↔ (∀ y, c y → y ⊑ x)))
    clear hex
    intro z ⟨hz, hnb⟩
    constructor
    · intro h y hy
      apply PartialOrder.rel_trans _ h; clear h
      cases hc y z hy hz
      next => assumption
      next h =>
        cases h
        · contradiction
        · constructor
    · intro h
      cases h z hz
      · contradiction
      · constructor
  next hnotex =>
    constructor
    · intro h y hy; clear h
      suffices y = b by rw [this]; exact FlatOrder.rel.bot
      rw [not_exists] at hnotex
      specialize hnotex y
      rw [not_and] at hnotex
      specialize hnotex hy
      rw [@Classical.not_not] at hnotex
      assumption
    · intro; exact FlatOrder.rel.bot

instance FlatOrder.instCCPO : CCPO (FlatOrder b) where
  has_csup hchain := ⟨flat_csup _ , flat_csup_is_sup _ hchain⟩

theorem flat_csup_eq (c : FlatOrder b → Prop) (hchain : chain c) :
    flat_csup c = CCPO.csup hchain := by
  apply is_sup_unique (c := c)
  · apply flat_csup_is_sup _ hchain
  · apply CCPO.csup_spec

theorem admissible_flatOrder (P : FlatOrder b → Prop) (hnot : P (.mk b b)) : admissible P := by
  intro c hchain h
  by_cases h' : ∃ (x : FlatOrder b), c x ∧ x ≠ b
  · simp [← flat_csup_eq, flat_csup, h']
    apply Classical.some_spec₂ (q := (P ·))
    intro x ⟨hcx, hneb⟩
    apply h x hcx
  · simp [← flat_csup_eq, flat_csup, h', hnot]

end flat_order

section mono_bind

/--
The class `MonoBind m` indicates that every `m α` has a `PartialOrder`, and that the bind operation
on `m` is monotone in both arguments with regard to that order.

This is intended to be used in the construction of `partial_fixpoint`, and not meant to be used otherwise.
-/
class MonoBind (m : Type u → Type v) [Bind m] [∀ α, PartialOrder (m α)] where
  bind_mono_left {a₁ a₂ : m α} {f : α → m β} (h : a₁ ⊑ a₂) : a₁ >>= f ⊑ a₂ >>= f
  bind_mono_right {a : m α} {f₁ f₂ : α → m β} (h : ∀ x, f₁ x ⊑ f₂ x) : a >>= f₁ ⊑ a >>= f₂

@[partial_fixpoint_monotone]
theorem monotone_bind
    (m : Type u → Type v) [Bind m] [∀ α, PartialOrder (m α)] [MonoBind m]
    {α β : Type u}
    {γ : Sort w} [PartialOrder γ]
    (f : γ → m α) (g : γ → α → m β)
    (hmono₁ : monotone f)
    (hmono₂ : monotone g) :
    monotone (fun (x : γ) => f x >>= g x) := by
  intro x₁ x₂ hx₁₂
  apply PartialOrder.rel_trans
  · apply MonoBind.bind_mono_left (hmono₁ _ _ hx₁₂)
  · apply MonoBind.bind_mono_right (fun y => monotone_apply y _ hmono₂ _ _ hx₁₂)

instance : PartialOrder (Option α) := inferInstanceAs (PartialOrder (FlatOrder none))
instance : CCPO (Option α) := inferInstanceAs (CCPO (FlatOrder none))
instance : MonoBind Option where
  bind_mono_left h := by
    cases h
    · exact FlatOrder.rel.bot
    · exact FlatOrder.rel.refl
  bind_mono_right h := by
    cases ‹Option _›
    · exact FlatOrder.rel.refl
    · exact h _

theorem Option.admissible_eq_some (P : Prop) (y : α) :
    admissible (fun (x : Option α) => x = some y → P) := by
  change admissible fun x : FlatOrder none => x = .mk _ (some y) → P
  apply admissible_flatOrder; simp

instance [inst : ∀ α, PartialOrder (m α)] : PartialOrder (ExceptT ε m α) := inst _
instance [inst : ∀ α, CCPO (m α)] : CCPO (ExceptT ε m α) := inst _
instance [Monad m] [∀ α, PartialOrder (m α)] [MonoBind m] : MonoBind (ExceptT ε m) where
  bind_mono_left h₁₂ := by
    apply MonoBind.bind_mono_left (m := m)
    exact h₁₂
  bind_mono_right h₁₂ := by
    apply MonoBind.bind_mono_right (m := m)
    intro x
    cases x
    · apply PartialOrder.rel_refl
    · apply h₁₂

@[partial_fixpoint_monotone]
theorem monotone_exceptTRun [PartialOrder γ]
    [Monad m] [∀ α, PartialOrder (m α)]
    (f : γ → ExceptT ε m α) (hmono : monotone f) :
    monotone (fun (x : γ) => ExceptT.run (f x)) :=
  hmono

instance [inst : ∀ α, PartialOrder (m α)] : PartialOrder (OptionT m α) := inst _
instance [inst : ∀ α, CCPO (m α)] : CCPO (OptionT m α) := inst _
instance [Monad m] [∀ α, PartialOrder (m α)] [MonoBind m] : MonoBind (OptionT m) where
  bind_mono_left h₁₂ := by
    apply MonoBind.bind_mono_left (m := m)
    exact h₁₂
  bind_mono_right h₁₂ := by
    apply MonoBind.bind_mono_right (m := m)
    intro x
    cases x
    · apply PartialOrder.rel_refl
    · apply h₁₂

@[partial_fixpoint_monotone]
theorem monotone_optionTRun [PartialOrder γ]
    [Monad m] [∀ α, PartialOrder (m α)]
    (f : γ → OptionT m α) (hmono : monotone f) :
    monotone (fun (x : γ) => OptionT.run (f x)) :=
  hmono

instance [inst : PartialOrder (m α)] : PartialOrder (ReaderT ρ m α) := instOrderPi
instance [inst : CCPO (m α)] : CCPO (ReaderT ρ m α) := instCCPOPi
instance [Monad m] [∀ α, PartialOrder (m α)] [MonoBind m] : MonoBind (ReaderT ρ m) where
  bind_mono_left h₁₂ := by
    intro x
    apply MonoBind.bind_mono_left (m := m)
    exact h₁₂ x
  bind_mono_right h₁₂ := by
    intro x
    apply MonoBind.bind_mono_right (m := m)
    intro y
    apply h₁₂

@[partial_fixpoint_monotone]
theorem monotone_readerTRun [PartialOrder γ]
    [Monad m] [PartialOrder (m α)]
    (f : γ → ReaderT σ m α) (hmono : monotone f) (s : σ) :
    monotone (fun (x : γ) => ReaderT.run (f x) s) :=
  monotone_apply s _ hmono

instance [inst : PartialOrder (m α)] : PartialOrder (StateRefT' ω σ m α) := instOrderPi
instance [inst : CCPO (m α)] : CCPO (StateRefT' ω σ m α) := instCCPOPi
instance [Monad m] [∀ α, PartialOrder (m α)] [MonoBind m] : MonoBind (StateRefT' ω σ m) :=
  inferInstanceAs (MonoBind (ReaderT (ST.Ref ω σ) m))

@[partial_fixpoint_monotone]
theorem monotone_stateRefT'Run [PartialOrder γ]
    [Monad m] [MonadLiftT (ST ω) m] [∀ α, PartialOrder (m α)] [MonoBind m]
    (f : γ → StateRefT' ω σ m α) (hmono : monotone f) (s : σ) :
    monotone (fun (x : γ) => StateRefT'.run (f x) s) := by
  apply monotone_bind
  · apply monotone_const
  · refine monotone_of_monotone_apply _ fun ref => ?_
    apply monotone_bind
    · exact monotone_apply _ _ hmono
    · apply monotone_const

instance [inst : ∀ α, PartialOrder (m α)] : PartialOrder (StateT σ m α) := instOrderPi
instance [inst : ∀ α, CCPO (m α)] : CCPO (StateT σ m α) := instCCPOPi
instance [Monad m] [∀ α, PartialOrder (m α)] [MonoBind m] : MonoBind (StateT ρ m) where
  bind_mono_left h₁₂ := by
    intro x
    apply MonoBind.bind_mono_left (m := m)
    exact h₁₂ x
  bind_mono_right h₁₂ := by
    intro x
    apply MonoBind.bind_mono_right (m := m)
    intro y
    apply h₁₂

@[partial_fixpoint_monotone]
theorem monotone_stateTRun [PartialOrder γ]
    [Monad m] [∀ α, PartialOrder (m α)]
    (f : γ → StateT σ m α) (hmono : monotone f) (s : σ) :
    monotone (fun (x : γ) => StateT.run (f x) s) :=
  monotone_apply s _ hmono

noncomputable def EST.bot [Nonempty ε] : EST ε σ α :=
  fun s => .error Classical.ofNonempty (Classical.choice ⟨s⟩)

-- Essentially
--   instance [Nonempty ε] : CCPO (EST ε σ α) :=
--     inferInstanceAs (CCPO ((s : _) → FlatOrder (EST.bot s)))
-- but hat would incur a noncomputable on the instance

instance [Nonempty ε] : CCPO (EST ε σ α) where
  rel := PartialOrder.rel (α := ∀ s, FlatOrder (EST.bot s))
  rel_refl := PartialOrder.rel_refl
  rel_antisymm := PartialOrder.rel_antisymm
  rel_trans := PartialOrder.rel_trans
  has_csup hchain := CCPO.has_csup (α := ∀ s, FlatOrder (EST.bot s)) hchain

instance [Nonempty ε] : MonoBind (EST ε σ) where
  bind_mono_left {_ _ a₁ a₂ f} h₁₂ := by
    intro s
    specialize h₁₂ s
    change FlatOrder.rel (a₁.bind f s) (a₂.bind f s)
    simp only [EST.bind]
    generalize a₁ s = a₁ at h₁₂; generalize a₂ s = a₂ at h₁₂
    cases h₁₂
    · exact .bot
    · exact .refl
  bind_mono_right {_ _ a f₁ f₂} h₁₂ := by
    intro w
    change FlatOrder.rel (a.bind f₁ w) (a.bind f₂ w)
    simp only [EST.bind]
    split
    · apply h₁₂
    · exact .refl

instance [Nonempty ε] : CCPO (EIO ε α) :=
  inferInstanceAs (CCPO (EST ε IO.RealWorld α))

instance [Nonempty ε] : MonoBind (EIO ε) :=
  inferInstanceAs (MonoBind (EST ε IO.RealWorld))

instance : CCPO (IO α) :=
  inferInstanceAs (CCPO (EIO IO.Error α))

instance : MonoBind IO :=
  inferInstanceAs (MonoBind (EIO IO.Error))

end mono_bind

section implication_order
-- Partial order on `Prop` given by implication
@[expose] def ImplicationOrder := Prop

instance ImplicationOrder.instOrder : PartialOrder ImplicationOrder where
  rel x y := x → y
  rel_refl := fun x => x
  rel_trans h₁ h₂ := fun x => h₂ (h₁  x)
  rel_antisymm h₁ h₂ := propext ⟨h₁, h₂⟩

-- This defines a complete lattice on `Prop`, used to define inductive predicates
instance ImplicationOrder.instCompleteLattice : CompleteLattice ImplicationOrder where
  has_sup c := by
    exists ∃ p, c p ∧ p
    intro x
    constructor
    case mp =>
      intro h y cy hy
      apply h
      apply Exists.intro y
      exact ⟨cy, hy⟩
    case mpr =>
      intro h
      intro e
      apply Exists.elim e
      intro a
      intro caa
      exact h a caa.1 caa.2

-- Monotonicity lemmas for inductive predicates
@[partial_fixpoint_monotone] theorem implication_order_monotone_exists
    {α} [PartialOrder α] {β} (f : α → β → ImplicationOrder)
    (h : monotone f) :
    @monotone _ _ _ ImplicationOrder.instOrder (fun x => (Exists (f x))) :=
  fun x y hxy ⟨w, hw⟩ => ⟨w, monotone_apply w f h x y hxy hw⟩

@[partial_fixpoint_monotone] theorem implication_order_monotone_forall
    {α} [PartialOrder α] {β} (f : α → β → ImplicationOrder)
    (h : monotone f) :
    @monotone _ _ _ ImplicationOrder.instOrder (fun x => ∀ y, f x y) :=
  fun x y hxy h₂ y₁ => monotone_apply y₁ f h x y hxy (h₂ y₁)

@[partial_fixpoint_monotone] theorem implication_order_monotone_and
    {α} [PartialOrder α] (f₁ : α → ImplicationOrder) (f₂ : α → ImplicationOrder)
    (h₁ : @monotone _ _ _ ImplicationOrder.instOrder f₁)
    (h₂ : @monotone _ _ _ ImplicationOrder.instOrder f₂) :
    @monotone _ _ _ ImplicationOrder.instOrder (fun x => f₁ x ∧ f₂ x) :=
  fun x y hxy ⟨hfx₁, hfx₂⟩ => ⟨h₁ x y hxy hfx₁, h₂ x y hxy hfx₂⟩

@[partial_fixpoint_monotone] theorem implication_order_monotone_or
    {α} [PartialOrder α] (f₁ : α → ImplicationOrder) (f₂ : α → ImplicationOrder)
    (h₁ : @monotone _ _ _ ImplicationOrder.instOrder f₁)
    (h₂ : @monotone _ _ _ ImplicationOrder.instOrder f₂) :
    @monotone _ _ _ ImplicationOrder.instOrder (fun x => f₁ x ∨ f₂ x) :=
  fun x y hxy h =>
    match h with
    | Or.inl hfx₁ => Or.inl (h₁ x y hxy hfx₁)
    | Or.inr hfx₂ => Or.inr (h₂ x y hxy hfx₂)

end implication_order

section reverse_implication_order

@[expose] def ReverseImplicationOrder := Prop

-- Partial order on `Prop` given by reverse implication
instance ReverseImplicationOrder.instOrder : PartialOrder ReverseImplicationOrder where
  rel x y := y → x
  rel_refl := fun x => x
  rel_trans := fun h₁ h₂ => fun x => h₁ (h₂ x)
  rel_antisymm h₁ h₂ := propext ⟨h₂, h₁⟩

-- This defines a complete lattice on `Prop`, used to define coinductive predicates
instance ReverseImplicationOrder.instCompleteLattice : CompleteLattice ReverseImplicationOrder where
  has_sup c := by
    exists ∀ p, c p → p
    intro x
    constructor
    case mp =>
      intro h y cy l
      apply h
      exact l
      exact cy
    case mpr =>
      intro h y cy ccy
      apply h
      exact ccy
      exact y

-- Monotonicity lemmas for coinductive predicates
@[partial_fixpoint_monotone] theorem coind_monotone_exists
    {α} [PartialOrder α] {β} (f : α → β → ReverseImplicationOrder)
    (h : monotone f) :
    @monotone _ _ _ ReverseImplicationOrder.instOrder (fun x => Exists (f x)) :=
  fun x y hxy ⟨w, hw⟩ => ⟨w, monotone_apply w f h x y hxy hw⟩

@[partial_fixpoint_monotone] theorem coind_monotone_forall
    {α} [PartialOrder α] {β} (f : α → β → ReverseImplicationOrder)
    (h : monotone f) :
    @monotone _ _ _ ReverseImplicationOrder.instOrder (fun x => ∀ y, f x y) :=
  fun x y hxy h₂ y₁ => monotone_apply y₁ f h x y hxy (h₂ y₁)

@[partial_fixpoint_monotone] theorem coind_monotone_and
    {α} [PartialOrder α] (f₁ : α → Prop) (f₂ : α → Prop)
    (h₁ : @monotone _ _ _ ReverseImplicationOrder.instOrder f₁)
    (h₂ : @monotone _ _ _ ReverseImplicationOrder.instOrder f₂) :
    @monotone _ _ _ ReverseImplicationOrder.instOrder (fun x => f₁ x ∧ f₂ x) :=
  fun x y hxy ⟨hfx₁, hfx₂⟩ => ⟨h₁ x y hxy hfx₁, h₂ x y hxy hfx₂⟩

@[partial_fixpoint_monotone] theorem coind_monotone_or
    {α} [PartialOrder α] (f₁ : α → Prop) (f₂ : α → Prop)
    (h₁ : @monotone _ _ _ ReverseImplicationOrder.instOrder f₁)
    (h₂ : @monotone _ _ _ ReverseImplicationOrder.instOrder f₂) :
    @monotone _ _ _ ReverseImplicationOrder.instOrder (fun x => f₁ x ∨ f₂ x) :=
  fun x y hxy h =>
    match h with
    | Or.inl hfx₁ => Or.inl (h₁ x y hxy hfx₁)
    | Or.inr hfx₂ => Or.inr (h₂ x y hxy hfx₂)
end reverse_implication_order

section antitone
@[partial_fixpoint_monotone] theorem coind_not
    {α} [PartialOrder α] (f₁ : α → Prop)
    (h₁ : @monotone _ _ _ ReverseImplicationOrder.instOrder f₁) :
    @monotone _ _ _ ImplicationOrder.instOrder (fun x => ¬f₁ x) := by
  intro x y hxy hfx h
  exact hfx (h₁ x y hxy h)

@[partial_fixpoint_monotone] theorem ind_not
    {α} [PartialOrder α] (f₁ : α → Prop)
    (h₁ : @monotone _ _ _ ImplicationOrder.instOrder f₁) :
    @monotone _ _ _ ReverseImplicationOrder.instOrder (fun x => ¬f₁ x) := by
  intro x y hxy hfx h
  exact hfx (h₁ x y hxy h)

@[partial_fixpoint_monotone] theorem ind_impl
    {α} [PartialOrder α] (f₁ : α → Prop) (f₂ : α → Prop)
    (h₁ : @monotone _ _ _ ReverseImplicationOrder.instOrder f₁)
    (h₂ : @monotone _ _ _ ImplicationOrder.instOrder f₂):
    @monotone _ _ _ ImplicationOrder.instOrder (fun x => f₁ x → f₂ x) := by
  intro x y hxy himp hf1
  specialize h₁ x y hxy hf1
  specialize h₂ x y hxy
  apply h₂
  apply himp
  exact h₁

@[partial_fixpoint_monotone] theorem coind_impl
    {α} [PartialOrder α] (f₁ : α → Prop) (f₂ : α → Prop)
    (h₁ : @monotone _ _ _ ImplicationOrder.instOrder f₁)
    (h₂ : @monotone _ _ _ ReverseImplicationOrder.instOrder f₂):
    @monotone _ _ _ ReverseImplicationOrder.instOrder (fun x => f₁ x → f₂ x) := by
  intro x y hxy himp hf1
  specialize h₁ x y hxy hf1
  specialize h₂ x y hxy
  apply h₂
  apply himp
  exact h₁
end antitone

namespace Example

def findF (P : Nat → Bool) (rec : Nat → Option Nat) (x : Nat) : Option Nat :=
  if P x then
    some x
  else
    rec (x + 1)

noncomputable def find (P : Nat → Bool) : Nat → Option Nat := fix (findF P) <| by
  unfold findF
  apply monotone_of_monotone_apply
  intro n
  split
  · apply monotone_const
  · apply monotone_apply
    apply monotone_id

theorem find_eq : find P = findF P (find P) := fix_eq ..

theorem find_spec : ∀ n m, find P n = some m → n ≤ m ∧ P m := by
  unfold find
  refine fix_induct (motive := fun (f : Nat → Option Nat) => ∀ n m, f n = some m → n ≤ m ∧ P m) _ ?hadm ?hstep
  case hadm =>
    -- apply admissible_pi_apply does not work well, hard to infer everything
    exact admissible_pi_apply _ (fun n => admissible_pi _ (fun m => Option.admissible_eq_some _ m))
  case hstep =>
    intro f ih n m heq
    simp only [findF] at heq
    split at heq
    · simp_all
    · obtain ⟨ih1, ih2⟩ := ih _ _ heq
      constructor
      · exact Nat.le_trans (Nat.le_add_right _ _ ) ih1
      · exact ih2

end Example

end Lean.Order
