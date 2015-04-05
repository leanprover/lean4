/-
copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LIcENSE.

Module: data.set.basic
Author: Jeremy Avigad, Leonardo de Moura
-/
import logic
open eq.ops

definition set (T : Type) := T → Prop

namespace set

variable {T : Type}

/- membership and subset -/

definition mem [reducible] (x : T) (a : set T) := a x
notation e ∈ a := mem e a

theorem setext {a b : set T} (H : ∀x, x ∈ a ↔ x ∈ b) : a = b :=
funext (take x, propext (H x))

definition subset (a b : set T) := ∀ x, x ∈ a → x ∈ b
infix `⊆`:50 := subset

/- bounded quantification -/

abbreviation bounded_forall (a : set T) (P : T → Prop) := ∀x, x ∈ a → P x
notation `forallb` binders `∈` a `,` r:(scoped:1 P, P) := bounded_forall a r
notation `∀₀` binders `∈` a `,` r:(scoped:1 P, P) := bounded_forall a r

abbreviation bounded_exists (a : set T) (P : T → Prop) := ∃x, x ∈ a ∧ P x
notation `existsb` binders `∈` a `,` r:(scoped:1 P, P) := bounded_exists a r
notation `∃₀` binders `∈` a `,` r:(scoped:1 P, P) := bounded_exists a r

/- empty set -/

definition empty [reducible] : set T := λx, false
notation `∅` := empty

theorem mem_empty (x : T) : ¬ (x ∈ ∅) :=
assume H : x ∈ ∅, H

/- universal set -/

definition univ : set T := λx, true

theorem mem_univ (x : T) : x ∈ univ := trivial

/- intersection -/

definition inter [reducible] (a b : set T) : set T := λx, x ∈ a ∧ x ∈ b
notation a ∩ b := inter a b

theorem mem_inter (x : T) (a b : set T) : x ∈ a ∩ b ↔ (x ∈ a ∧ x ∈ b) := !iff.refl

theorem inter_self (a : set T) : a ∩ a = a :=
setext (take x, !and_self)

theorem inter_empty (a : set T) : a ∩ ∅ = ∅ :=
setext (take x, !and_false)

theorem empty_inter (a : set T) : ∅ ∩ a = ∅ :=
setext (take x, !false_and)

theorem inter.comm (a b : set T) : a ∩ b = b ∩ a :=
setext (take x, !and.comm)

theorem inter.assoc (a b c : set T) : (a ∩ b) ∩ c = a ∩ (b ∩ c) :=
setext (take x, !and.assoc)

/- union -/

definition union [reducible] (a b : set T) : set T := λx, x ∈ a ∨ x ∈ b
notation a ∪ b := union a b

theorem mem_union (x : T) (a b : set T) : x ∈ a ∪ b ↔ (x ∈ a ∨ x ∈ b) := !iff.refl

theorem union_self (a : set T) : a ∪ a = a :=
setext (take x, !or_self)

theorem union_empty (a : set T) : a ∪ ∅ = a :=
setext (take x, !or_false)

theorem empty_union (a : set T) : ∅ ∪ a = a :=
setext (take x, !false_or)

theorem union.comm (a b : set T) : a ∪ b = b ∪ a :=
setext (take x, or.comm)

theorem union_assoc (a b c : set T) : (a ∪ b) ∪ c = a ∪ (b ∪ c) :=
setext (take x, or.assoc)

/- set-builder notation -/

-- {x : T | P}
definition set_of (P : T → Prop) : set T := P
notation `{` binders `|` r:(scoped:1 P, set_of P) `}` := r

-- {[x, y, z]} or ⦃x, y, z⦄
definition insert (x : T) (a : set T) : set T := {y : T | y = x ∨ y ∈ a}
notation `{[`:max a:(foldr `,` (x b, insert x b) ∅) `]}`:0 := a
notation `⦃` a:(foldr `,` (x b, insert x b) ∅) `⦄` := a

/- large unions -/

section
  variables {I : Type}
  variable a : set I
  variable b : I → set T
  variable C : set (set T)

  definition Inter  : set T := {x : T | ∀i, x ∈ b i}
  definition bInter : set T := {x : T | ∀₀ i ∈ a, x ∈ b i}
  definition sInter : set T := {x : T | ∀₀ c ∈ C, x ∈ c}
  definition Union  : set T := {x : T | ∃i, x ∈ b i}
  definition bUnion : set T := {x : T | ∃₀ i ∈ a, x ∈ b i}
  definition sUnion : set T := {x : T | ∃₀ c ∈ C, x ∈ c}

  -- TODO: need notation for these
end

end set
