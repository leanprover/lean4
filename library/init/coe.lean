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
universe variables u v

structure [class] has_lift (A : Type u) (B : Type v) :=
(lift : A → B)

/- Auxiliary class that contains the transitive closure of has_lift. -/
structure [class] has_lift_t (A : Type u) (B : Type v) :=
(lift : A → B)

structure [class] has_coe (A : Type u) (B : Type v) :=
(coe : A → B)

/- Auxiliary class that contains the transitive closure of has_coe. -/
structure [class] has_coe_t (A : Type u) (B : Type v) :=
(coe : A → B)

structure [class] has_coe_to_fun (A : Type u) : Type (max u (v+1)) :=
(F : Type v) (coe : A → F)

structure [class] has_coe_to_sort (A : Type u) : Type (max u (v+1)) :=
(S : Type v) (coe : A → S)

definition lift {A : Type u} {B : Type v} [has_lift A B] : A → B :=
@has_lift.lift A B _

definition lift_t {A : Type u} {B : Type v} [has_lift_t A B] : A → B :=
@has_lift_t.lift A B _

definition coe_b {A : Type u} {B : Type v} [has_coe A B] : A → B :=
@has_coe.coe A B _

definition coe_t {A : Type u} {B : Type v} [has_coe_t A B] : A → B :=
@has_coe_t.coe A B _

set_option pp.all true
definition coe_fn_b {A : Type u} [has_coe_to_fun.{u v} A] : A → has_coe_to_fun.F.{u v} A :=
has_coe_to_fun.coe

/- User level coercion operators -/

definition coe {A : Type u} {B : Type v} [has_lift_t A B] : A → B :=
lift_t

definition coe_fn {A : Type u} [has_coe_to_fun.{u v} A] : A → has_coe_to_fun.F.{u v} A :=
has_coe_to_fun.coe

definition coe_sort {A : Type u} [has_coe_to_sort.{u v} A] : A → has_coe_to_sort.S.{u v} A :=
has_coe_to_sort.coe

/- Notation -/

notation `↑`:max a:max := coe a

notation `⇑`:max a:max := coe_fn a

notation `↥`:max a:max := coe_sort a

/- Transitive closure for has_lift, has_coe, has_coe_to_fun -/

attribute [instance]
definition {u₁ u₂ u₃} lift_trans {A : Type u₁} {B : Type u₂} {C : Type u₃} [has_lift A B] [has_lift_t B C] : has_lift_t A C :=
⟨λ a, lift_t (lift a : B)⟩

attribute [instance]
definition lift_base {A : Type u} {B : Type v} [has_lift A B] : has_lift_t A B :=
⟨lift⟩

attribute [instance]
definition {u₁ u₂ u₃} coe_trans {A : Type u₁} {B : Type u₂} {C : Type u₃} [has_coe A B] [has_coe_t B C] : has_coe_t A C :=
⟨λ a, coe_t (coe_b a : B)⟩

attribute [instance]
definition coe_base {A : Type u} {B : Type v} [has_coe A B] : has_coe_t A B :=
⟨coe_b⟩

attribute [instance]
definition {u₁ u₂ u₃} coe_fn_trans {A : Type u₁} {B : Type u₂} [has_lift_t A B] [has_coe_to_fun.{u₂ u₃} B] : has_coe_to_fun.{u₁ u₃} A :=
⟨has_coe_to_fun.F B, λ a, coe_fn (coe a)⟩

attribute [instance]
definition {u₁ u₂ u₃} coe_sort_trans {A : Type u₁} {B : Type u₂} [has_lift_t A B] [has_coe_to_sort.{u₂ u₃} B] : has_coe_to_sort.{u₁ u₃} A :=
⟨has_coe_to_sort.S B, λ a, coe_sort (coe a)⟩

/- Every coercion is also a lift -/

attribute [instance]
definition coe_to_lift {A : Type u} {B : Type v} [has_coe_t A B] : has_lift_t A B :=
⟨coe_t⟩

/- Basic coercions -/

attribute [instance]
definition coe_bool_to_Prop : has_coe bool Prop :=
⟨λ b, b = tt⟩

attribute [instance]
definition coe_decidable_eq (b : bool) : decidable (coe b) :=
show decidable (b = tt), from bool.has_decidable_eq b tt

attribute [instance]
definition coe_subtype {A : Type u} {p : A → Prop} : has_coe {a // p a} A :=
⟨λ s, subtype.elt_of s⟩

/- Basic lifts -/

/- Remark: we can't use [has_lift_t A₂ A₁] since it will produce non-termination whenever a type class resolution
   problem does not have a solution. -/
attribute [instance]
definition {ua₁ ua₂ ub₁ ub₂} lift_fn {A₁ : Type ua₁} {A₂ : Type ua₂} {B₁ : Type ub₁} {B₂ : Type ub₂} [has_lift A₂ A₁] [has_lift_t B₁ B₂] : has_lift (A₁ → B₁) (A₂ → B₂) :=
⟨λ f a, ↑(f ↑a)⟩

attribute [instance]
definition {ua ub₁ ub₂} lift_fn_range {A : Type ua} {B₁ : Type ub₁} {B₂ : Type ub₂} [has_lift_t B₁ B₂] : has_lift (A → B₁) (A → B₂) :=
⟨λ f a, ↑(f a)⟩

attribute [instance]
definition {ua₁ ua₂ ub} lift_fn_dom {A₁ : Type ua₁} {A₂ : Type ua₂} {B : Type ub} [has_lift A₂ A₁] : has_lift (A₁ → B) (A₂ → B) :=
⟨λ f a, f ↑a⟩

attribute [instance]
definition {ua₁ ua₂ ub₁ ub₂} lift_pair {A₁ : Type ua₁} {A₂ : Type ub₂} {B₁ : Type ub₁} {B₂ : Type ub₂} [has_lift_t A₁ A₂] [has_lift_t B₁ B₂] : has_lift (A₁ × B₁) (A₂ × B₂) :=
⟨λ p, prod.cases_on p (λ a b, (↑a, ↑b))⟩

attribute [instance]
definition {ua₁ ua₂ ub} lift_pair₁ {A₁ : Type ua₁} {A₂ : Type ua₂} {B : Type ub} [has_lift_t A₁ A₂] : has_lift (A₁ × B) (A₂ × B) :=
⟨λ p, prod.cases_on p (λ a b, (↑a, b))⟩

attribute [instance]
definition {ua ub₁ ub₂} lift_pair₂ {A : Type ua} {B₁ : Type ub₁} {B₂ : Type ub₂} [has_lift_t B₁ B₂] : has_lift (A × B₁) (A × B₂) :=
⟨λ p, prod.cases_on p (λ a b, (a, ↑b))⟩

attribute [instance]
definition lift_list {A : Type u} {B : Type v} [has_lift_t A B] : has_lift (list A) (list B) :=
⟨λ l, list.map (@coe A B _) l⟩
