/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Jeremy Avigad, Leonardo de Moura
-/
import logic.connectives logic.identities algebra.binary
open eq.ops binary function

definition set (X : Type) := X → Prop

namespace set

variable {X : Type}

/- membership and subset -/

definition mem (x : X) (a : set X) := a x
infix ∈ := mem
notation a ∉ b := ¬ mem a b

theorem ext {a b : set X} (H : ∀x, x ∈ a ↔ x ∈ b) : a = b :=
funext (take x, propext (H x))

definition subset (a b : set X) := ∀⦃x⦄, x ∈ a → x ∈ b
infix ⊆ := subset

definition superset (s t : set X) : Prop := t ⊆ s
infix ⊇ := superset

theorem subset.refl (a : set X) : a ⊆ a := take x, assume H, H

theorem subset.trans {a b c : set X} (subab : a ⊆ b) (subbc : b ⊆ c) : a ⊆ c :=
take x, assume ax, subbc (subab ax)

theorem subset.antisymm {a b : set X} (h₁ : a ⊆ b) (h₂ : b ⊆ a) : a = b :=
ext (λ x, iff.intro (λ ina, h₁ ina) (λ inb, h₂ inb))

-- an alterantive name
theorem eq_of_subset_of_subset {a b : set X} (h₁ : a ⊆ b) (h₂ : b ⊆ a) : a = b :=
subset.antisymm h₁ h₂

theorem mem_of_subset_of_mem {s₁ s₂ : set X} {a : X} : s₁ ⊆ s₂ → a ∈ s₁ → a ∈ s₂ :=
assume h₁ h₂, h₁ _ h₂

/- strict subset -/

definition strict_subset (a b : set X) := a ⊆ b ∧ a ≠ b
infix ` ⊂ `:50 := strict_subset

theorem strict_subset.irrefl (a : set X) : ¬ a ⊂ a :=
assume h, absurd rfl (and.elim_right h)

/- bounded quantification -/

abbreviation bounded_forall (a : set X) (P : X → Prop) := ∀⦃x⦄, x ∈ a → P x
notation `forallb` binders `∈` a `, ` r:(scoped:1 P, P) := bounded_forall a r
notation `∀₀` binders `∈` a `, ` r:(scoped:1 P, P) := bounded_forall a r

abbreviation bounded_exists (a : set X) (P : X → Prop) := ∃⦃x⦄, x ∈ a ∧ P x
notation `existsb` binders `∈` a `, ` r:(scoped:1 P, P) := bounded_exists a r
notation `∃₀` binders `∈` a `, ` r:(scoped:1 P, P) := bounded_exists a r

theorem bounded_exists.intro {P : X → Prop} {s : set X} {x : X} (xs : x ∈ s) (Px : P x) :
  ∃₀ x ∈ s, P x :=
exists.intro x (and.intro xs Px)

/- empty set -/

definition empty : set X := λx, false
notation `∅` := empty

theorem not_mem_empty (x : X) : ¬ (x ∈ ∅) :=
assume H : x ∈ ∅, H

theorem mem_empty_eq (x : X) : x ∈ ∅ = false := rfl

theorem eq_empty_of_forall_not_mem {s : set X} (H : ∀ x, x ∉ s) : s = ∅ :=
ext (take x, iff.intro
  (assume xs, absurd xs (H x))
  (assume xe, absurd xe !not_mem_empty))

section
  open classical

  theorem exists_mem_of_ne_empty {s : set X} (H : s ≠ ∅) : ∃ x, x ∈ s :=
  by_contradiction (assume H', H (eq_empty_of_forall_not_mem (forall_not_of_not_exists H')))
end

theorem empty_subset (s : set X) : ∅ ⊆ s :=
take x, assume H, false.elim H

theorem eq_empty_of_subset_empty {s : set X} (H : s ⊆ ∅) : s = ∅ :=
subset.antisymm H (empty_subset s)

theorem subset_empty_iff (s : set X) : s ⊆ ∅ ↔ s = ∅ :=
iff.intro eq_empty_of_subset_empty (take xeq, by rewrite xeq; apply subset.refl ∅)

/- universal set -/

definition univ : set X := λx, true

theorem mem_univ (x : X) : x ∈ univ := trivial

theorem mem_univ_iff (x : X) : x ∈ univ ↔ true := !iff.refl

theorem mem_univ_eq (x : X) : x ∈ univ = true := rfl

theorem empty_ne_univ [h : inhabited X] : (empty : set X) ≠ univ :=
assume H : empty = univ,
absurd (mem_univ (inhabited.value h)) (eq.rec_on H (not_mem_empty _))

theorem subset_univ (s : set X) : s ⊆ univ := λ x H, trivial

theorem eq_univ_of_univ_subset {s : set X} (H : univ ⊆ s) : s = univ :=
eq_of_subset_of_subset (subset_univ s) H

theorem eq_univ_of_forall {s : set X} (H : ∀ x, x ∈ s) : s = univ :=
ext (take x, iff.intro (assume H', trivial) (assume H', H x))

/- union -/

definition union (a b : set X) : set X := λx, x ∈ a ∨ x ∈ b
notation a ∪ b := union a b

theorem mem_union_left {x : X} {a : set X} (b : set X) : x ∈ a → x ∈ a ∪ b :=
assume h, or.inl h

theorem mem_union_right {x : X} {b : set X} (a : set X) : x ∈ b → x ∈ a ∪ b :=
assume h, or.inr h

theorem mem_unionl {x : X} {a b : set X} : x ∈ a → x ∈ a ∪ b :=
assume h, or.inl h

theorem mem_unionr {x : X} {a b : set X} : x ∈ b → x ∈ a ∪ b :=
assume h, or.inr h

theorem mem_or_mem_of_mem_union {x : X} {a b : set X} (H : x ∈ a ∪ b) : x ∈ a ∨ x ∈ b := H

theorem mem_union.elim {x : X} {a b : set X} {P : Prop}
    (H₁ : x ∈ a ∪ b) (H₂ : x ∈ a → P) (H₃ : x ∈ b → P) : P :=
or.elim H₁ H₂ H₃

theorem mem_union_iff (x : X) (a b : set X) : x ∈ a ∪ b ↔ x ∈ a ∨ x ∈ b := !iff.refl

theorem mem_union_eq (x : X) (a b : set X) : x ∈ a ∪ b = (x ∈ a ∨ x ∈ b) := rfl

theorem union_self (a : set X) : a ∪ a = a :=
ext (take x, !or_self)

theorem union_empty (a : set X) : a ∪ ∅ = a :=
ext (take x, !or_false)

theorem empty_union (a : set X) : ∅ ∪ a = a :=
ext (take x, !false_or)

theorem union_comm (a b : set X) : a ∪ b = b ∪ a :=
ext (take x, or.comm)

theorem union_assoc (a b c : set X) : (a ∪ b) ∪ c = a ∪ (b ∪ c) :=
ext (take x, or.assoc)

theorem union_left_comm (s₁ s₂ s₃ : set X) : s₁ ∪ (s₂ ∪ s₃) = s₂ ∪ (s₁ ∪ s₃) :=
!left_comm union_comm union_assoc s₁ s₂ s₃

theorem union_right_comm (s₁ s₂ s₃ : set X) : (s₁ ∪ s₂) ∪ s₃ = (s₁ ∪ s₃) ∪ s₂ :=
!right_comm union_comm union_assoc s₁ s₂ s₃

theorem subset_union_left (s t : set X) : s ⊆ s ∪ t := λ x H, or.inl H

theorem subset_union_right (s t : set X) : t ⊆ s ∪ t := λ x H, or.inr H

theorem union_subset {s t r : set X} (sr : s ⊆ r) (tr : t ⊆ r) : s ∪ t ⊆ r :=
λ x xst, or.elim xst (λ xs, sr xs) (λ xt, tr xt)

/- intersection -/

definition inter (a b : set X) : set X := λx, x ∈ a ∧ x ∈ b
notation a ∩ b := inter a b

theorem mem_inter_iff (x : X) (a b : set X) : x ∈ a ∩ b ↔ x ∈ a ∧ x ∈ b := !iff.refl

theorem mem_inter_eq (x : X) (a b : set X) : x ∈ a ∩ b = (x ∈ a ∧ x ∈ b) := rfl

theorem mem_inter {x : X} {a b : set X} (Ha : x ∈ a) (Hb : x ∈ b) : x ∈ a ∩ b :=
and.intro Ha Hb

theorem mem_of_mem_inter_left {x : X} {a b : set X} (H : x ∈ a ∩ b) : x ∈ a :=
and.left H

theorem mem_of_mem_inter_right {x : X} {a b : set X} (H : x ∈ a ∩ b) : x ∈ b :=
and.right H

theorem inter_self (a : set X) : a ∩ a = a :=
ext (take x, !and_self)

theorem inter_empty (a : set X) : a ∩ ∅ = ∅ :=
ext (take x, !and_false)

theorem empty_inter (a : set X) : ∅ ∩ a = ∅ :=
ext (take x, !false_and)

theorem inter_comm (a b : set X) : a ∩ b = b ∩ a :=
ext (take x, !and.comm)

theorem inter_assoc (a b c : set X) : (a ∩ b) ∩ c = a ∩ (b ∩ c) :=
ext (take x, !and.assoc)

theorem inter_left_comm (s₁ s₂ s₃ : set X) : s₁ ∩ (s₂ ∩ s₃) = s₂ ∩ (s₁ ∩ s₃) :=
!left_comm inter_comm inter_assoc s₁ s₂ s₃

theorem inter_right_comm (s₁ s₂ s₃ : set X) : (s₁ ∩ s₂) ∩ s₃ = (s₁ ∩ s₃) ∩ s₂ :=
!right_comm inter_comm inter_assoc s₁ s₂ s₃

theorem inter_univ (a : set X) : a ∩ univ = a :=
ext (take x, !and_true)

theorem univ_inter (a : set X) : univ ∩ a = a :=
ext (take x, !true_and)

theorem inter_subset_left (s t : set X) : s ∩ t ⊆ s := λ x H, and.left H

theorem inter_subset_right (s t : set X) : s ∩ t ⊆ t := λ x H, and.right H

theorem subset_inter {s t r : set X} (rs : r ⊆ s) (rt : r ⊆ t) : r ⊆ s ∩ t :=
λ x xr, and.intro (rs xr) (rt xr)

/- distributivity laws -/

theorem inter_distrib_left (s t u : set X) : s ∩ (t ∪ u) = (s ∩ t) ∪ (s ∩ u) :=
ext (take x, !and.left_distrib)

theorem inter_distrib_right (s t u : set X) : (s ∪ t) ∩ u = (s ∩ u) ∪ (t ∩ u) :=
ext (take x, !and.right_distrib)

theorem union_distrib_left (s t u : set X) : s ∪ (t ∩ u) = (s ∪ t) ∩ (s ∪ u) :=
ext (take x, !or.left_distrib)

theorem union_distrib_right (s t u : set X) : (s ∩ t) ∪ u = (s ∪ u) ∩ (t ∪ u) :=
ext (take x, !or.right_distrib)

/- set-builder notation -/

-- {x : X | P}
definition set_of (P : X → Prop) : set X := P
notation `{` binder ` | ` r:(scoped:1 P, set_of P) `}` := r

-- {x ∈ s | P}
definition sep (P : X → Prop) (s : set X) : set X := λx, x ∈ s ∧ P x
notation `{` binder ` ∈ ` s ` | ` r:(scoped:1 p, sep p s) `}` := r

/- insert -/

definition insert (x : X) (a : set X) : set X := {y : X | y = x ∨ y ∈ a}

-- '{x, y, z}
notation `'{`:max a:(foldr `, ` (x b, insert x b) ∅) `}`:0 := a

theorem subset_insert (x : X) (a : set X) : a ⊆ insert x a :=
take y, assume ys, or.inr ys

theorem mem_insert (x : X) (s : set X) : x ∈ insert x s :=
or.inl rfl

theorem mem_insert_of_mem {x : X} {s : set X} (y : X) : x ∈ s → x ∈ insert y s :=
assume h, or.inr h

theorem eq_or_mem_of_mem_insert {x a : X} {s : set X} : x ∈ insert a s → x = a ∨ x ∈ s :=
assume h, h

theorem mem_of_mem_insert_of_ne {x a : X} {s : set X} (xin : x ∈ insert a s) : x ≠ a → x ∈ s :=
or_resolve_right (eq_or_mem_of_mem_insert xin)

theorem mem_insert_eq (x a : X) (s : set X) : x ∈ insert a s = (x = a ∨ x ∈ s) :=
propext (iff.intro !eq_or_mem_of_mem_insert
  (or.rec (λH', (eq.substr H' !mem_insert)) !mem_insert_of_mem))

theorem insert_eq_of_mem {a : X} {s : set X} (H : a ∈ s) : insert a s = s :=
ext (λ x, eq.substr (mem_insert_eq x a s)
   (or_iff_right_of_imp (λH1, eq.substr H1 H)))

theorem insert.comm (x y : X) (s : set X) : insert x (insert y s) = insert y (insert x s) :=
ext (take a, by rewrite [*mem_insert_eq, propext !or.left_comm])

-- useful in proofs by induction
theorem forall_of_forall_insert {P : X → Prop} {a : X} {s : set X}
    (H : ∀ x, x ∈ insert a s → P x) :
  ∀ x, x ∈ s → P x :=
λ x xs, H x (!mem_insert_of_mem xs)

/- singleton -/

theorem mem_singleton_iff (a b : X) : a ∈ '{b} ↔ a = b :=
iff.intro
  (assume ainb, or.elim ainb (λ aeqb, aeqb) (λ f, false.elim f))
  (assume aeqb, or.inl aeqb)

theorem mem_singleton (a : X) : a ∈ '{a} := !mem_insert

theorem eq_of_mem_singleton {x y : X} (h : x ∈ '{y}) : x = y :=
or.elim (eq_or_mem_of_mem_insert h)
  (suppose x = y, this)
  (suppose x ∈ ∅, absurd this !not_mem_empty)

theorem mem_singleton_of_eq {x y : X} (H : x = y) : x ∈ '{y} :=
eq.symm H ▸ mem_singleton y

theorem insert_eq (x : X) (s : set X) : insert x s = '{x} ∪ s :=
ext (take y, iff.intro
  (suppose y ∈ insert x s,
    or.elim this (suppose y = x, or.inl (or.inl this)) (suppose y ∈ s, or.inr this))
  (suppose y ∈ '{x} ∪ s,
    or.elim this
      (suppose y ∈ '{x}, or.inl (eq_of_mem_singleton this))
      (suppose y ∈ s, or.inr this)))

/- separation -/

theorem mem_sep {s : set X} {P : X → Prop} {x : X} (xs : x ∈ s) (Px : P x) : x ∈ {x ∈ s | P x} :=
and.intro xs Px

theorem eq_sep_of_subset {s t : set X} (ssubt : s ⊆ t) : s = {x ∈ t | x ∈ s} :=
ext (take x, iff.intro
  (suppose x ∈ s, and.intro (ssubt this) this)
  (suppose x ∈ {x ∈ t | x ∈ s}, and.right this))

theorem mem_sep_iff {s : set X} {P : X → Prop} {x : X} : x ∈ {x ∈ s | P x} ↔ x ∈ s ∧ P x :=
!iff.refl

theorem sep_subset (s : set X) (P : X → Prop) : {x ∈ s | P x} ⊆ s :=
take x, assume H, and.left H

/- complement -/

definition complement (s : set X) : set X := {x | x ∉ s}
prefix `-` := complement

theorem mem_comp {s : set X} {x : X} (H : x ∉ s) : x ∈ -s := H

theorem not_mem_of_mem_comp {s : set X} {x : X} (H : x ∈ -s) : x ∉ s := H

theorem mem_comp_iff (s : set X) (x : X) : x ∈ -s ↔ x ∉ s := !iff.refl

theorem inter_comp_self (s : set X) : s ∩ -s = ∅ :=
ext (take x, !and_not_self_iff)

theorem comp_inter_self (s : set X) : -s ∩ s = ∅ :=
ext (take x, !not_and_self_iff)

/- some classical identities -/

section
  open classical

  theorem comp_empty : -(∅ : set X) = univ :=
  ext (take x, iff.intro (assume H, trivial) (assume H, not_false))

  theorem comp_union (s t : set X) : -(s ∪ t) = -s ∩ -t :=
  ext (take x, !not_or_iff_not_and_not)

  theorem comp_comp (s : set X) : -(-s) = s :=
  ext (take x, !not_not_iff)

  theorem comp_inter (s t : set X) : -(s ∩ t) = -s ∪ -t :=
  ext (take x, !not_and_iff_not_or_not)

  theorem comp_univ : -(univ : set X) = ∅ :=
  by rewrite [-comp_empty, comp_comp]

  theorem union_eq_comp_comp_inter_comp (s t : set X) : s ∪ t = -(-s ∩ -t) :=
  ext (take x, !or_iff_not_and_not)

  theorem inter_eq_comp_comp_union_comp (s t : set X) : s ∩ t = -(-s ∪ -t) :=
  ext (take x, !and_iff_not_or_not)

  theorem union_comp_self (s : set X) : s ∪ -s = univ :=
  ext (take x, !or_not_self_iff)

  theorem comp_union_self (s : set X) : -s ∪ s = univ :=
  ext (take x, !not_or_self_iff)

  theorem complement_compose_complement :
    #function complement ∘ complement = @id (set X) :=
  funext (λ s, comp_comp s)
end

/- set difference -/

definition diff (s t : set X) : set X := {x ∈ s | x ∉ t}
infix `\`:70 := diff

theorem mem_diff {s t : set X} {x : X} (H1 : x ∈ s) (H2 : x ∉ t) : x ∈ s \ t :=
and.intro H1 H2

theorem mem_of_mem_diff {s t : set X} {x : X} (H : x ∈ s \ t) : x ∈ s :=
and.left H

theorem not_mem_of_mem_diff {s t : set X} {x : X} (H : x ∈ s \ t) : x ∉ t :=
and.right H

theorem mem_diff_iff (s t : set X) (x : X) : x ∈ s \ t ↔ x ∈ s ∧ x ∉ t := !iff.refl

theorem mem_diff_eq (s t : set X) (x : X) : x ∈ s \ t = (x ∈ s ∧ x ∉ t) := rfl

theorem diff_eq (s t : set X) : s \ t = s ∩ -t := rfl

theorem union_diff_cancel {s t : set X} [dec : Π x, decidable (x ∈ s)] (H : s ⊆ t) : s ∪ (t \ s) = t :=
ext (take x, iff.intro
  (assume H1 : x ∈ s ∪ (t \ s), or.elim H1 (assume H2, !H H2) (assume H2, and.left H2))
  (assume H1 : x ∈ t,
    decidable.by_cases
      (suppose x ∈ s, or.inl this)
      (suppose x ∉ s, or.inr (and.intro H1 this))))

theorem diff_subset (s t : set X) : s \ t ⊆ s := inter_subset_left s _

theorem comp_eq_univ_diff (s : set X) : -s = univ \ s :=
ext (take x, iff.intro (assume H, and.intro trivial H) (assume H, and.right H))

/- powerset -/

definition powerset (s : set X) : set (set X) := {x : set X | x ⊆ s}
prefix `𝒫`:100 := powerset

theorem mem_powerset {x s : set X} (H : x ⊆ s) : x ∈ 𝒫 s := H

theorem subset_of_mem_powerset {x s : set X} (H : x ∈ 𝒫 s) : x ⊆ s := H

theorem mem_powerset_iff (x s : set X) : x ∈ 𝒫 s ↔ x ⊆ s := !iff.refl

/- function image -/

section image

variables {Y Z : Type}

abbreviation eq_on (f1 f2 : X → Y) (a : set X) : Prop :=
∀₀ x ∈ a, f1 x = f2 x

definition image (f : X → Y) (a : set X) : set Y := {y : Y | ∃x, x ∈ a ∧ f x = y}
infix `'` := image

theorem image_eq_image_of_eq_on {f1 f2 : X → Y} {a : set X} (H1 : eq_on f1 f2 a) :
  f1 ' a = f2 ' a :=
ext (take y, iff.intro
  (assume H2,
    obtain x (H3 : x ∈ a ∧ f1 x = y), from H2,
    have H4 : x ∈ a, from and.left H3,
    have H5 : f2 x = y, from (H1 H4)⁻¹ ⬝ and.right H3,
    exists.intro x (and.intro H4 H5))
  (assume H2,
    obtain x (H3 : x ∈ a ∧ f2 x = y), from H2,
    have H4 : x ∈ a, from and.left H3,
    have H5 : f1 x = y, from (H1 H4) ⬝ and.right H3,
    exists.intro x (and.intro H4 H5)))

theorem mem_image {f : X → Y} {a : set X} {x : X} {y : Y}
  (H1 : x ∈ a) (H2 : f x = y) : y ∈ f ' a :=
exists.intro x (and.intro H1 H2)

theorem mem_image_of_mem (f : X → Y) {x : X} {a : set X} (H : x ∈ a) : f x ∈ image f a :=
mem_image H rfl

lemma image_compose (f : Y → Z) (g : X → Y) (a : set X) : (f ∘ g) ' a = f ' (g ' a) :=
ext (take z,
  iff.intro
    (assume Hz : z ∈ (f ∘ g) ' a,
      obtain x (Hx₁ : x ∈ a) (Hx₂ : f (g x) = z), from Hz,
      have Hgx : g x ∈ g ' a, from mem_image Hx₁ rfl,
      show z ∈ f ' (g ' a), from mem_image Hgx Hx₂)
    (assume Hz : z ∈ f ' (g 'a),
      obtain y (Hy₁ : y ∈ g ' a) (Hy₂ : f y = z), from Hz,
      obtain x (Hz₁ : x ∈ a) (Hz₂ : g x = y),      from Hy₁,
      show z ∈ (f ∘ g) ' a, from mem_image Hz₁ (Hz₂⁻¹ ▸ Hy₂)))

lemma image_subset {a b : set X} (f : X → Y) (H : a ⊆ b) : f ' a ⊆ f ' b :=
take y, assume Hy : y ∈ f ' a,
obtain x (Hx₁ : x ∈ a) (Hx₂ : f x = y), from Hy,
mem_image (H Hx₁) Hx₂

theorem image_union (f : X → Y) (s t : set X) :
  image f (s ∪ t) = image f s ∪ image f t :=
ext (take y, iff.intro
  (assume H : y ∈ image f (s ∪ t),
    obtain x [(xst : x ∈ s ∪ t) (fxy : f x = y)], from H,
    or.elim xst
      (assume xs, or.inl (mem_image xs fxy))
      (assume xt, or.inr (mem_image xt fxy)))
  (assume H : y ∈ image f s ∪ image f t,
    or.elim H
      (assume yifs : y ∈ image f s,
        obtain x [(xs : x ∈ s) (fxy : f x = y)], from yifs,
        mem_image (or.inl xs) fxy)
      (assume yift : y ∈ image f t,
        obtain x [(xt : x ∈ t) (fxy : f x = y)], from yift,
        mem_image (or.inr xt) fxy)))

theorem image_empty (f : X → Y) : image f ∅ = ∅ :=
eq_empty_of_forall_not_mem
  (take y, suppose y ∈ image f ∅,
    obtain x [(H : x ∈ empty) H'], from this,
    H)

theorem mem_image_complement (t : set X) (S : set (set X)) :
  t ∈ complement ' S ↔ -t ∈ S :=
iff.intro
  (suppose t ∈ complement ' S,
    obtain t' [(Ht' : t' ∈ S) (Ht : -t' = t)], from this,
    show -t ∈ S, by rewrite [-Ht, comp_comp]; exact Ht')
  (suppose -t ∈ S,
    have -(-t) ∈ complement 'S, from mem_image_of_mem complement this,
    show t ∈ complement 'S, from comp_comp t ▸ this)

theorem image_id (s : set X) : id ' s = s :=
ext (take x, iff.intro
  (suppose x ∈ id ' s,
    obtain x' [(Hx' : x' ∈ s) (x'eq : x' = x)], from this,
    show x ∈ s, by rewrite [-x'eq]; apply Hx')
  (suppose x ∈ s, mem_image_of_mem id this))

theorem complement_complement_image (S : set (set X)) :
  complement ' (complement ' S) = S :=
by rewrite [-image_compose, complement_compose_complement, image_id]

end image

/- collections of disjoint sets -/

definition disjoint_sets (S : set (set X)) : Prop := ∀ a b, a ∈ S → b ∈ S → a ≠ b → a ∩ b = ∅

theorem disjoint_sets_empty : disjoint_sets (∅ : set (set X)) :=
take a b, assume H, !not.elim !not_mem_empty H

theorem disjoint_sets_union {s t : set (set X)} (Hs : disjoint_sets s) (Ht : disjoint_sets t)
    (H : ∀ x y, x ∈ s ∧ y ∈ t → x ∩ y = ∅) :
  disjoint_sets (s ∪ t) :=
take a b, assume Ha Hb Hneq, or.elim Ha
 (assume H1, or.elim Hb
   (suppose b ∈ s, (Hs a b) H1 this Hneq)
   (suppose b ∈ t, (H a b) (and.intro H1 this)))
 (assume H2, or.elim Hb
   (suppose b ∈ s, !inter_comm ▸ ((H b a) (and.intro this H2)))
   (suppose b ∈ t, (Ht a b) H2 this Hneq))

theorem disjoint_sets_singleton (s : set (set X)) : disjoint_sets '{s} :=
take a b, assume Ha Hb  Hneq,
absurd (eq.trans ((iff.elim_left !mem_singleton_iff) Ha) ((iff.elim_left !mem_singleton_iff) Hb)⁻¹)
    Hneq

/- large unions -/

section large_unions
  variables {I : Type}
  variable a : set I
  variable b : I → set X
  variable C : set (set X)

  definition sUnion : set X := {x : X | ∃₀ c ∈ C, x ∈ c}
  definition sInter : set X := {x : X | ∀₀ c ∈ C, x ∈ c}

  prefix `⋃₀`:110 := sUnion
  prefix `⋂₀`:110 := sInter

  definition Union  : set X := {x : X | ∃i, x ∈ b i}
  definition Inter  : set X := {x : X | ∀i, x ∈ b i}

  notation `⋃` binders `, ` r:(scoped f, Union f) := r
  notation `⋂` binders `, ` r:(scoped f, Inter f) := r

  definition bUnion : set X := {x : X | ∃₀ i ∈ a, x ∈ b i}
  definition bInter : set X := {x : X | ∀₀ i ∈ a, x ∈ b i}

  notation `⋃` binders ` ∈ ` s `, ` r:(scoped f, bUnion s f) := r
  notation `⋂` binders ` ∈ ` s `, ` r:(scoped f, bInter s f) := r

end large_unions

-- sUnion and sInter: a collection (set) of sets

theorem mem_sUnion {x : X} {t : set X} {S : set (set X)} (Hx : x ∈ t) (Ht : t ∈ S) :
  x ∈ ⋃₀ S :=
exists.intro t (and.intro Ht Hx)

theorem mem_sInter {x : X} {t : set X} {S : set (set X)} (H : ∀₀ t ∈ S, x ∈ t) :
  x ∈ ⋂₀ S :=
H

theorem sInter_subset_of_mem {S : set (set X)} {t : set X} (tS : t ∈ S) :
  (⋂₀ S) ⊆ t :=
take x, assume H, H t tS

theorem subset_sUnion_of_mem {S : set (set X)} {t : set X} (tS : t ∈ S) :
  t ⊆ (⋃₀ S) :=
take x, assume H, exists.intro t (and.intro tS H)

theorem sUnion_empty : ⋃₀ ∅ = (∅ : set X) :=
eq_empty_of_forall_not_mem
  (take x, suppose x ∈ sUnion ∅,
    obtain t [(Ht : t ∈ ∅) Ht'], from this,
    show false, from Ht)

theorem sInter_empty : ⋂₀ ∅ = (univ : set X) :=
eq_univ_of_forall (λ x s H, false.elim H)

theorem sUnion_singleton (s : set X) : ⋃₀ '{s} = s :=
ext (take x, iff.intro
  (suppose x ∈ sUnion '{s},
    obtain u [(Hu : u ∈ '{s}) (xu : x ∈ u)], from this,
    have u = s, from eq_of_mem_singleton Hu,
    show x ∈ s, using this, by rewrite -this; apply xu)
  (suppose x ∈ s,
    mem_sUnion this (mem_singleton s)))

theorem sInter_singleton (s : set X) : ⋂₀ '{s} = s :=
ext (take x, iff.intro
  (suppose x ∈ ⋂₀ '{s}, show x ∈ s, from this (mem_singleton s))
  (suppose x ∈ s, take u, suppose u ∈ '{s},
    show x ∈ u, by+ rewrite [eq_of_mem_singleton this]; assumption))

theorem sUnion_union (S T : set (set X)) : ⋃₀ (S ∪ T) = ⋃₀ S ∪ ⋃₀ T :=
ext (take x, iff.intro
  (suppose x ∈ sUnion (S ∪ T),
    obtain u [(Hu : u ∈ S ∪ T) (xu : x ∈ u)], from this,
    or.elim Hu
      (assume uS, or.inl (mem_sUnion xu uS))
      (assume uT, or.inr (mem_sUnion xu uT)))
  (suppose x ∈ sUnion S ∪ sUnion T,
    or.elim this
      (suppose x ∈ sUnion S,
        obtain u [(uS : u ∈ S) (xu : x ∈ u)], from this,
        mem_sUnion xu (or.inl uS))
      (suppose x ∈ sUnion T,
        obtain u [(uT : u ∈ T) (xu : x ∈ u)], from this,
        mem_sUnion xu (or.inr uT))))

theorem sInter_union (S T : set (set X)) : ⋂₀ (S ∪ T) = ⋂₀ S ∩ ⋂₀ T :=
ext (take x, iff.intro
  (assume H : x ∈ ⋂₀ (S ∪ T),
    and.intro (λ u uS, H (or.inl uS)) (λ u uT, H (or.inr uT)))
  (assume H : x ∈ ⋂₀ S ∩ ⋂₀ T,
    take u, suppose u ∈ S ∪ T, or.elim this (λ uS, and.left H u uS) (λ uT, and.right H u uT)))

theorem sUnion_insert (s : set X) (T : set (set X)) :
  ⋃₀ (insert s T) = s ∪ ⋃₀ T :=
by rewrite [insert_eq, sUnion_union, sUnion_singleton]

theorem sInter_insert (s : set X) (T : set (set X)) :
  ⋂₀ (insert s T) = s ∩ ⋂₀ T :=
by rewrite [insert_eq, sInter_union, sInter_singleton]

theorem comp_sUnion (S : set (set X)) :
  - ⋃₀ S = ⋂₀ (complement ' S) :=
ext (take x, iff.intro
  (assume H : x ∈ -(⋃₀ S),
    take t, suppose t ∈ complement ' S,
    obtain t' [(Ht' : t' ∈ S) (Ht : -t' = t)], from this,
    have x ∈ -t', from suppose x ∈ t', H (mem_sUnion this Ht'),
    show x ∈ t, using this, by rewrite -Ht; apply this)
  (assume H : x ∈ ⋂₀ (complement ' S),
    suppose x ∈ ⋃₀ S,
    obtain t [(tS : t ∈ S) (xt : x ∈ t)], from this,
    have -t ∈ complement ' S, from mem_image_of_mem complement tS,
    have x ∈ -t, from H this,
    show false, proof this xt qed))

theorem sUnion_eq_comp_sInter_comp (S : set (set X)) :
  ⋃₀ S = - ⋂₀ (complement ' S) :=
by rewrite [-comp_comp, comp_sUnion]

theorem comp_sInter (S : set (set X)) :
  - ⋂₀ S = ⋃₀ (complement ' S) :=
by rewrite [sUnion_eq_comp_sInter_comp, complement_complement_image]

theorem sInter_eq_comp_sUnion_comp (S : set (set X)) :
   ⋂₀ S = -(⋃₀ (complement ' S)) :=
by rewrite [-comp_comp, comp_sInter]

-- Union and Inter: a family of sets indexed by a type

theorem Union_subset {I : Type} {b : I → set X} {c : set X} (H : ∀ i, b i ⊆ c) : (⋃ i, b i) ⊆ c :=
take x,
suppose x ∈ Union b,
obtain i (Hi : x ∈ b i), from this,
show x ∈ c, from H i Hi

theorem subset_Inter {I : Type} {b : I → set X} {c : set X} (H : ∀ i, c ⊆ b i) : c ⊆ ⋂ i, b i :=
λ x cx i, H i cx

theorem Union_eq_sUnion_image {X I : Type} (s : I → set X) : (⋃ i, s i) = ⋃₀ (s ' univ) :=
ext (take x, iff.intro
  (suppose x ∈ Union s,
    obtain i (Hi : x ∈ s i), from this,
    mem_sUnion Hi (mem_image_of_mem s trivial))
  (suppose x ∈ sUnion (s ' univ),
    obtain t [(Ht : t ∈ s ' univ) (Hx : x ∈ t)], from this,
    obtain i [univi (Hi : s i = t)], from Ht,
    exists.intro i (show x ∈ s i, by rewrite Hi; apply Hx)))

theorem Inter_eq_sInter_image {X I : Type} (s : I → set X) : (⋂ i, s i) = ⋂₀ (s ' univ) :=
ext (take x, iff.intro
  (assume H : x ∈ Inter s,
    take t,
    suppose t ∈ s 'univ,
    obtain i [univi (Hi : s i = t)], from this,
    show x ∈ t, by rewrite -Hi; exact H i)
  (assume H : x ∈ ⋂₀ (s ' univ),
    take i,
    have s i ∈ s ' univ, from mem_image_of_mem s trivial,
    show x ∈ s i, from H this))

theorem comp_Union {X I : Type} (s : I → set X) : - (⋃ i, s i) = (⋂ i, - s i) :=
by rewrite [Union_eq_sUnion_image, comp_sUnion, -image_compose, -Inter_eq_sInter_image]

theorem comp_Inter {X I : Type} (s : I → set X) : -(⋂ i, s i) = (⋃ i, - s i) :=
by rewrite [Inter_eq_sInter_image, comp_sInter, -image_compose, -Union_eq_sUnion_image]

theorem Union_eq_comp_Inter_comp {X I : Type} (s : I → set X) : (⋃ i, s i) = - (⋂ i, - s i) :=
by rewrite [-comp_comp, comp_Union]

theorem Inter_eq_comp_Union_comp {X I : Type} (s : I → set X) : (⋂ i, s i) = - (⋃ i, -s i) :=
by rewrite [-comp_comp, comp_Inter]

-- these are useful for turning binary union / intersection into countable ones

definition bin_ext (s t : set X) (n : ℕ) : set X :=
nat.cases_on n s (λ m, t)

lemma Union_bin_ext (s t : set X) : (⋃ i, bin_ext s t i) = s ∪ t :=
ext (take x, iff.intro
  (assume H,
    obtain i (Hi : x ∈ (bin_ext s t) i), from H,
    by cases i; apply or.inl Hi; apply or.inr Hi)
  (assume H,
    or.elim H
      (suppose x ∈ s, exists.intro 0 this)
      (suppose x ∈ t, exists.intro 1 this)))

lemma Inter_bin_ext (s t : set X) : (⋂ i, bin_ext s t i) = s ∩ t :=
ext (take x, iff.intro
  (assume H, and.intro (H 0) (H 1))
  (assume H, by intro i; cases i;
    apply and.elim_left H; apply and.elim_right H))

-- bUnion and bInter: a family of sets indexed by a set ("b" is for bounded)

variable {Y : Type}

theorem mem_bUnion {s : set X} {f : X → set Y} {x : X} {y : Y}
    (xs : x ∈ s) (yfx : y ∈ f x) :
  y ∈ ⋃ x ∈ s, f x :=
exists.intro x (and.intro xs yfx)

theorem mem_bInter {s : set X} {f : X → set Y} {y : Y} (H : ∀₀ x ∈ s, y ∈ f x) :
  y ∈ ⋂ x ∈ s, f x :=
H

theorem bUnion_subset {s : set X} {t : set Y} {f : X → set Y} (H : ∀₀ x ∈ s, f x ⊆ t) :
  (⋃ x ∈ s, f x) ⊆ t :=
take y, assume Hy,
obtain x [xs yfx], from Hy,
show y ∈ t, from H xs yfx

theorem subset_bInter {s : set X} {t : set Y} {f : X → set Y} (H : ∀₀ x ∈ s, t ⊆ f x) :
  t ⊆ ⋂ x ∈ s, f x :=
take y, assume yt, take x, assume xs, H xs yt

theorem subset_bUnion_of_mem {s : set X} {f : X → set Y} {x : X} (xs : x ∈ s) :
  f x ⊆ ⋃ x ∈ s, f x :=
take y, assume Hy, mem_bUnion xs Hy

theorem bInter_subset_of_mem {s : set X} {f : X → set Y} {x : X} (xs : x ∈ s) :
  (⋂ x ∈ s, f x) ⊆ f x :=
take y, assume Hy, Hy x xs

end set
