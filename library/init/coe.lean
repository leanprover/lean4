/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/

/-
The elaborator tries to insert coercions automatically.
Only instances of has_coe type class are considered in the process.

Lean also provides a "lifting" operator: ↑a.
It uses all instances of has_lift type class.
Every has_coe instance is also a has_lift instance.

We recommend users only use has_coe for coercions that do not produce a lot
of ambiguity.

All coercions and lifts can be identified with the constant coe.

We also have a has_coe_to_fun type class for encoding coercions from
a type to a function space.
-/
prelude
import init.list init.subtype init.prod

structure has_lift [class] (A B : Type) :=
(lift : A → B)

/- Auxiliary class that contains the transitive closure of has_lift. -/
structure has_lift_t [class] (A B : Type) :=
(lift : A → B)

structure has_coe [class] (A B : Type) :=
(coe : A → B)

/- Auxiliary class that contains the transitive closure of has_coe. -/
structure has_coe_t [class] (A B : Type) :=
(coe : A → B)

structure has_coe_to_fun [class] (A : Type) :=
(F : Type) (coe : A → F)

definition lift {A B : Type} [has_lift A B] : A → B :=
@has_lift.lift A B _

definition lift_t {A B : Type} [has_lift_t A B] : A → B :=
@has_lift_t.lift A B _

definition coe_b {A B : Type} [has_coe A B] : A → B :=
@has_coe.coe A B _

definition coe_t {A B : Type} [has_coe_t A B] : A → B :=
@has_coe_t.coe A B _

definition coe_fn_b {A : Type} [has_coe_to_fun A] : A → has_coe_to_fun.F A :=
has_coe_to_fun.coe

/- User level coercion operators -/

definition coe {A B : Type} [has_lift_t A B] : A → B :=
lift_t

definition coe_fn {A : Type} [has_coe_to_fun A] : A → has_coe_to_fun.F A :=
has_coe_to_fun.coe

/- Notation -/

notation `↑`:max a:max := coe a

notation `⇑`:max a:max := coe_fn a

/- Transitive closure for has_lift, has_coe, has_coe_to_fun -/

definition lift_base [instance] {A B : Type} [has_lift A B] : has_lift_t A B :=
has_lift_t.mk lift

definition lift_trans [instance] {A B C : Type} [has_lift A B] [has_lift_t B C] : has_lift_t A C :=
has_lift_t.mk (λ a, lift_t (lift a : B))

definition coe_base [instance] {A B : Type} [has_coe A B] : has_coe_t A B :=
has_coe_t.mk coe_b

definition coe_trans [instance] {A B C : Type} [has_coe A B] [has_coe_t B C] : has_coe_t A C :=
has_coe_t.mk (λ a, coe_t (coe_b a : B))

definition coe_fn_trans [instance] {A B : Type} [has_lift_t A B] [has_coe_to_fun B] : has_coe_to_fun A :=
has_coe_to_fun.mk (has_coe_to_fun.F B) (λ a, coe_fn (coe a))

/- Every coercion is also a lift -/

definition coe_to_lift [instance] {A B : Type} [has_coe_t A B] : has_lift_t A B :=
has_lift_t.mk coe_t

/- Basic coercions -/

definition coe_bool_to_Prop [instance] : has_coe bool Prop :=
has_coe.mk (λ b, b = tt)

definition coe_subtype [instance] {A : Type} {P : A → Prop} : has_coe {a \ P a} A :=
has_coe.mk (λ s, subtype.elt_of s)

/- Basic lifts -/

/- Remark: we can't use [has_lift_t A₂ A₁] since it will produce non-termination whenever a type class resolution
   problem does not have a solution. -/
definition lift_fn [instance] {A₁ A₂ B₁ B₂ : Type} [has_lift A₂ A₁] [has_lift_t B₁ B₂] : has_lift (A₁ → B₁) (A₂ → B₂) :=
has_lift.mk (λ f a, ↑(f ↑a))

definition lift_fn_range [instance] {A B₁ B₂ : Type} [has_lift_t B₁ B₂] : has_lift (A → B₁) (A → B₂) :=
has_lift.mk (λ f a, ↑(f a))

definition lift_fn_dom [instance] {A₁ A₂ B : Type} [has_lift A₂ A₁] : has_lift (A₁ → B) (A₂ → B) :=
has_lift.mk (λ f a, f ↑a)

definition lift_pair [instance] {A₁ A₂ B₁ B₂ : Type} [has_lift_t A₁ A₂] [has_lift_t B₁ B₂] : has_lift (A₁ × B₁) (A₂ × B₂) :=
has_lift.mk (λ p, prod.cases_on p (λ a b, (↑a, ↑b)))

definition lift_pair₁ [instance] {A₁ A₂ B : Type} [has_lift_t A₁ A₂] : has_lift (A₁ × B) (A₂ × B) :=
has_lift.mk (λ p, prod.cases_on p (λ a b, (↑a, b)))

definition lift_pair₂ [instance] {A B₁ B₂ : Type} [has_lift_t B₁ B₂] : has_lift (A × B₁) (A × B₂) :=
has_lift.mk (λ p, prod.cases_on p (λ a b, (a, ↑b)))

definition lift_list [instance] {A B : Type} [has_lift_t A B] : has_lift (list A) (list B) :=
has_lift.mk (λ l, list.map (@coe A B _) l)
