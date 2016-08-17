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

We use the has_coe_to_fun type class for encoding coercions from
a type to a function space.

We use the has_coe_to_sort type class for encoding coercions from
a type to a sort.
-/
prelude
import init.list init.subtype init.prod

structure [class] has_lift (A B : Type) :=
(lift : A → B)

/- Auxiliary class that contains the transitive closure of has_lift. -/
structure [class] has_lift_t (A B : Type) :=
(lift : A → B)

structure [class] has_coe (A B : Type) :=
(coe : A → B)

/- Auxiliary class that contains the transitive closure of has_coe. -/
structure [class] has_coe_t (A B : Type) :=
(coe : A → B)

structure [class] has_coe_to_fun (A : Type) :=
(F : Type) (coe : A → F)

structure [class] has_coe_to_sort (A : Type) :=
(S : Type) (coe : A → S)

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

definition coe_sort {A : Type} [has_coe_to_sort A] : A → has_coe_to_sort.S A :=
has_coe_to_sort.coe

/- Notation -/

notation `↑`:max a:max := coe a

notation `⇑`:max a:max := coe_fn a

notation `↥`:max a:max := coe_sort a

/- Transitive closure for has_lift, has_coe, has_coe_to_fun -/

attribute [instance]
definition lift_trans {A B C : Type} [has_lift A B] [has_lift_t B C] : has_lift_t A C :=
has_lift_t.mk (λ a, lift_t (lift a : B))

attribute [instance]
definition lift_base {A B : Type} [has_lift A B] : has_lift_t A B :=
has_lift_t.mk lift

attribute [instance]
definition coe_trans {A B C : Type} [has_coe A B] [has_coe_t B C] : has_coe_t A C :=
has_coe_t.mk (λ a, coe_t (coe_b a : B))

attribute [instance]
definition coe_base {A B : Type} [has_coe A B] : has_coe_t A B :=
has_coe_t.mk coe_b

attribute [instance]
definition coe_fn_trans {A B : Type} [has_lift_t A B] [has_coe_to_fun B] : has_coe_to_fun A :=
has_coe_to_fun.mk (has_coe_to_fun.F B) (λ a, coe_fn (coe a))

attribute [instance]
definition coe_sort_trans {A B : Type} [has_lift_t A B] [has_coe_to_sort B] : has_coe_to_sort A :=
has_coe_to_sort.mk (has_coe_to_sort.S B) (λ a, coe_sort (coe a))

/- Every coercion is also a lift -/

attribute [instance]
definition coe_to_lift {A B : Type} [has_coe_t A B] : has_lift_t A B :=
has_lift_t.mk coe_t

/- Basic coercions -/

attribute [instance]
definition coe_bool_to_Prop : has_coe bool Prop :=
has_coe.mk (λ b, b = tt)

attribute [instance]
definition coe_decidable_eq (b : bool) : decidable (coe b) :=
show decidable (b = tt), from _

attribute [instance]
definition coe_subtype {A : Type} {P : A → Prop} : has_coe {a \ P a} A :=
has_coe.mk (λ s, subtype.elt_of s)

/- Basic lifts -/

/- Remark: we can't use [has_lift_t A₂ A₁] since it will produce non-termination whenever a type class resolution
   problem does not have a solution. -/
attribute [instance]
definition lift_fn {A₁ A₂ B₁ B₂ : Type} [has_lift A₂ A₁] [has_lift_t B₁ B₂] : has_lift (A₁ → B₁) (A₂ → B₂) :=
has_lift.mk (λ f a, ↑(f ↑a))

attribute [instance]
definition lift_fn_range {A B₁ B₂ : Type} [has_lift_t B₁ B₂] : has_lift (A → B₁) (A → B₂) :=
has_lift.mk (λ f a, ↑(f a))

attribute [instance]
definition lift_fn_dom {A₁ A₂ B : Type} [has_lift A₂ A₁] : has_lift (A₁ → B) (A₂ → B) :=
has_lift.mk (λ f a, f ↑a)

attribute [instance]
definition lift_pair {A₁ A₂ B₁ B₂ : Type} [has_lift_t A₁ A₂] [has_lift_t B₁ B₂] : has_lift (A₁ × B₁) (A₂ × B₂) :=
has_lift.mk (λ p, prod.cases_on p (λ a b, (↑a, ↑b)))

attribute [instance]
definition lift_pair₁ {A₁ A₂ B : Type} [has_lift_t A₁ A₂] : has_lift (A₁ × B) (A₂ × B) :=
has_lift.mk (λ p, prod.cases_on p (λ a b, (↑a, b)))

attribute [instance]
definition lift_pair₂ {A B₁ B₂ : Type} [has_lift_t B₁ B₂] : has_lift (A × B₁) (A × B₂) :=
has_lift.mk (λ p, prod.cases_on p (λ a b, (a, ↑b)))

attribute [instance]
definition lift_list {A B : Type} [has_lift_t A B] : has_lift (list A) (list B) :=
has_lift.mk (λ l, list.map (@coe A B _) l)
