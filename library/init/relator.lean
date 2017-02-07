/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl

Relator for functions, pairs, sums, and lists.
-/

prelude
import init.core init.data.basic

namespace relator
universe variables u₁ u₂ v₁ v₂

reserve infixr ` ⇒ `:40

/- TODO(johoelzl):
 * should we introduce relators of datatypes as recursive function or as inductive
predicate? For now we stick to the recursor approach.
 * relation lift for datatypes, Π, Σ, set, and subtype types
 * proof composition and identity laws
 * implement method to derive relators from datatype
-/

section
variables {α : Type u₁} {β : Type u₂} {γ : Type v₁} {δ : Type v₂}
variables (R : α → β → Prop) (S : γ → δ → Prop)

def lift_fun (f : α → γ) (g : β → δ) : Prop :=
∀{a b}, R a b → S (f a) (g b)

infixr ⇒ := lift_fun

end

section
variables {α : Type u₁} {β : out_param (Type u₂)} (R : out_param (α → β → Prop))

@[class] def right_total := ∀b, ∃a, R a b
@[class] def left_total := ∀a, ∃b, R a b
@[class] def bi_total := left_total R ∧ right_total R

end

section
variables {α : Type u₁} {β : Type u₂} (R : α → β → Prop)

@[class] def left_unique := ∀{a b c}, R a b → R c b → a = c
@[class] def right_unique := ∀{a b c}, R a b → R a c → b = c

lemma rel_forall_of_total [t : bi_total R] : ((R ⇒ iff) ⇒ iff) (λp, ∀i, p i) (λq, ∀i, q i) :=
take p q Hrel,
  ⟨take H b, exists.elim (t^.right b) (take a Rab, (Hrel Rab)^.mp (H _)),
    take H a, exists.elim (t^.left a) (take b Rab, (Hrel Rab)^.mpr (H _))⟩

lemma left_unique_of_rel_eq {eq' : β → β → Prop} (he : (R ⇒ (R ⇒ iff)) eq eq') : left_unique R
| a b c (ab : R a b) (cb : R c b) :=
have eq' b b,
  from iff.mp (he ab ab) rfl,
iff.mpr (he ab cb) this

end

lemma rel_imp : (iff ⇒ (iff  ⇒ iff)) implies implies :=
take p q h r s l, imp_congr h l

lemma rel_not : (iff ⇒ iff) not not :=
take p q h, not_congr h

end relator
