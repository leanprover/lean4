/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Jeremy Avigad, Leonardo de Moura
-/
import logic.connectives logic.identities algebra.binary
open eq.ops binary

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

theorem union.comm (a b : set X) : a ∪ b = b ∪ a :=
ext (take x, or.comm)

theorem union.assoc (a b c : set X) : (a ∪ b) ∪ c = a ∪ (b ∪ c) :=
ext (take x, or.assoc)

theorem union.left_comm (s₁ s₂ s₃ : set X) : s₁ ∪ (s₂ ∪ s₃) = s₂ ∪ (s₁ ∪ s₃) :=
!left_comm union.comm union.assoc s₁ s₂ s₃

theorem union.right_comm (s₁ s₂ s₃ : set X) : (s₁ ∪ s₂) ∪ s₃ = (s₁ ∪ s₃) ∪ s₂ :=
!right_comm union.comm union.assoc s₁ s₂ s₃

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

theorem inter.comm (a b : set X) : a ∩ b = b ∩ a :=
ext (take x, !and.comm)

theorem inter.assoc (a b c : set X) : (a ∩ b) ∩ c = a ∩ (b ∩ c) :=
ext (take x, !and.assoc)

theorem inter.left_comm (s₁ s₂ s₃ : set X) : s₁ ∩ (s₂ ∩ s₃) = s₂ ∩ (s₁ ∩ s₃) :=
!left_comm inter.comm inter.assoc s₁ s₂ s₃

theorem inter.right_comm (s₁ s₂ s₃ : set X) : (s₁ ∩ s₂) ∩ s₃ = (s₁ ∩ s₃) ∩ s₂ :=
!right_comm inter.comm inter.assoc s₁ s₂ s₃

theorem inter_univ (a : set X) : a ∩ univ = a :=
ext (take x, !and_true)

theorem univ_inter (a : set X) : univ ∩ a = a :=
ext (take x, !true_and)

theorem inter_subset_left (s t : set X) : s ∩ t ⊆ s := λ x H, and.left H

theorem inter_subset_right (s t : set X) : s ∩ t ⊆ t := λ x H, and.right H

theorem subset_inter {s t r : set X} (rs : r ⊆ s) (rt : r ⊆ t) : r ⊆ s ∩ t :=
λ x xr, and.intro (rs xr) (rt xr)

/- distributivity laws -/

theorem inter.distrib_left (s t u : set X) : s ∩ (t ∪ u) = (s ∩ t) ∪ (s ∩ u) :=
ext (take x, !and.left_distrib)

theorem inter.distrib_right (s t u : set X) : (s ∪ t) ∩ u = (s ∩ u) ∪ (t ∩ u) :=
ext (take x, !and.right_distrib)

theorem union.distrib_left (s t u : set X) : s ∪ (t ∩ u) = (s ∪ t) ∩ (s ∪ u) :=
ext (take x, !or.left_distrib)

theorem union.distrib_right (s t u : set X) : (s ∩ t) ∪ u = (s ∪ u) ∩ (t ∪ u) :=
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

/- singleton -/

theorem mem_singleton_iff (a b : X) : a ∈ '{b} ↔ a = b :=
iff.intro
  (assume ainb, or.elim ainb (λ aeqb, aeqb) (λ f, false.elim f))
  (assume aeqb, or.inl aeqb)

theorem mem_singleton (a : X) : a ∈ '{a} := !mem_insert

theorem eq_of_mem_singleton {x y : X} : x ∈ insert y ∅ → x = y :=
assume h, or.elim (eq_or_mem_of_mem_insert h)
  (suppose x = y, this)
  (suppose x ∈ ∅, absurd this !not_mem_empty)

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

  theorem union_eq_comp_comp_inter_comp (s t : set X) : s ∪ t = -(-s ∩ -t) :=
  ext (take x, !or_iff_not_and_not)

  theorem inter_eq_comp_comp_union_comp (s t : set X) : s ∩ t = -(-s ∪ -t) :=
  ext (take x, !and_iff_not_or_not)

  theorem union_comp_self (s : set X) : s ∪ -s = univ :=
  ext (take x, !or_not_self_iff)

  theorem comp_union_self (s : set X) : -s ∪ s = univ :=
  ext (take x, !not_or_self_iff)
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

/- powerset -/

definition powerset (s : set X) : set (set X) := {x : set X | x ⊆ s}
prefix `𝒫`:100 := powerset

theorem mem_powerset {x s : set X} (H : x ⊆ s) : x ∈ 𝒫 s := H

theorem subset_of_mem_powerset {x s : set X} (H : x ∈ 𝒫 s) : x ⊆ s := H

theorem mem_powerset_iff (x s : set X) : x ∈ 𝒫 s ↔ x ⊆ s := !iff.refl

/- large unions -/

section
  variables {I : Type}
  variable a : set I
  variable b : I → set X
  variable C : set (set X)

  definition Inter  : set X := {x : X | ∀i, x ∈ b i}
  definition bInter : set X := {x : X | ∀₀ i ∈ a, x ∈ b i}
  definition sInter : set X := {x : X | ∀₀ c ∈ C, x ∈ c}
  definition Union  : set X := {x : X | ∃i, x ∈ b i}
  definition bUnion : set X := {x : X | ∃₀ i ∈ a, x ∈ b i}
  definition sUnion : set X := {x : X | ∃₀ c ∈ C, x ∈ c}

  -- TODO: need notation for these

  theorem Union_subset {b : I → set X} {c : set X} (H : ∀ i, b i ⊆ c) : Union b ⊆ c :=
  take x,
  suppose x ∈ Union b,
  obtain i (Hi : x ∈ b i), from this,
  show x ∈ c, from H i Hi
  
  theorem sUnion_insert (s : set (set X)) (a : set X) :  
  sUnion (insert a s) = a ∪ sUnion s := 
ext (take x, iff.intro
  (suppose x ∈ sUnion (insert a s),
    obtain c [(cias : c ∈ insert a s) (xc : x ∈ c)], from this,
    or.elim cias
      (suppose c = a,
        show x ∈ a ∪ sUnion s, from or.inl (this ▸ xc))
      (suppose c ∈ s,
        show x ∈ a ∪ sUnion s, from or.inr (exists.intro c (and.intro this xc))))
  (suppose x ∈ a ∪ sUnion s,
    or.elim this
      (suppose x ∈ a,
        have a ∈ insert a s, from or.inl rfl,
        show x ∈ sUnion (insert a s), from exists.intro a (and.intro this `x ∈ a`))
      (suppose x ∈ sUnion s,
        obtain c [(cs : c ∈ s) (xc : x ∈ c)], from this,
        have c ∈ insert a s, from or.inr cs,
        show x ∈ sUnion (insert a s), from exists.intro c (and.intro this `x ∈ c`))))
        
  lemma sInter_insert (s : set (set X)) (a : set X) :
  sInter (insert a s) = a ∩ sInter s := 
ext (take x, iff.intro
  (suppose x ∈ sInter (insert a s), 
    have ∀c, c ∈ insert a s → x ∈ c, from this,
    have x ∈ a, from (this a) !mem_insert,
    show x ∈ a ∩ sInter s, from and.intro
      `x ∈ a`
      take c,
      suppose c ∈ s,
        (`∀c, c ∈ insert a s → x ∈ c` c) (!mem_insert_of_mem this))
  (suppose x ∈ a ∩ sInter s,
    show ∀c, c ∈ insert a s → x ∈ c, from 
    take c,
    suppose c ∈ insert a s,
    have c = a → x ∈ c, from 
      suppose c = a,
      show x ∈ c, from this⁻¹ ▸ and.elim_left `x ∈ a ∩ sInter s`,
    have c ∈ s → x ∈ c, from 
      suppose c ∈ s,
      have ∀c, c ∈ s → x ∈ c, from and.elim_right `x ∈ a ∩ sInter s`, 
      show x ∈ c, from (this c) `c ∈ s`,
    show x ∈ c, from !or.elim `c ∈ insert a s` `c = a → x ∈ c` this))
    
end

end set
