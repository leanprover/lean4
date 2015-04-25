/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Module: data.squash
Author: Leonardo de Moura

Define squash type (aka propositional truncation) using quotients.
This definition is slightly better than defining the squash type ∥A∥ as (nonempty A).
If we define it using (nonempty A), then we can only lift functions A → B to ∥A∥ → B
when B is a proposition. With quotients, we can lift to any B type that is a subsingleton
(i.e., has at most one element).
-/
open quot

private definition eqv {A : Type} (a b : A) : Prop := true
local infix ~ := eqv

private lemma eqv_refl {A : Type} : ∀ a : A, a ~ a :=
λ a, trivial

private lemma eqv_symm {A : Type} : ∀ a b : A, a ~ b → b ~ a :=
λ a b h, trivial

private lemma eqv_trans {A : Type} : ∀ a b c : A, a ~ b → b ~ c → a ~ c :=
λ a b c h₁ h₂, trivial

definition squash_setoid (A : Type) : setoid A :=
setoid.mk (@eqv A) (mk_equivalence (@eqv A) (@eqv_refl A) (@eqv_symm A) (@eqv_trans A))

definition squash (A : Type) : Type :=
quot (squash_setoid A)

namespace squash
local attribute squash_setoid [instance]

notation `∥`:0 A `∥` := squash A

definition mk {A : Type} (a : A) : ∥A∥ :=
⟦a⟧

protected definition irrelevant {A : Type} : ∀ a b : ∥A∥, a = b :=
λ a b, quot.induction_on₂ a b (λ a b, quot.sound trivial)

definition lift {A B : Type} [h : subsingleton B] (f : A → B) : ∥A∥ → B :=
λ s, quot.lift_on s f (λ a₁ a₂ r, subsingleton.elim (f a₁) (f a₂))
end squash

open squash decidable

definition decidable_eq_squash [instance] (A : Type) : decidable_eq ∥A∥ :=
λ a b, inl (squash.irrelevant a b)

definition subsingleton_squash [instance] (A : Type) : subsingleton ∥A∥ :=
subsingleton.intro (@squash.irrelevant A)
