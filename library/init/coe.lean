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

class has_lift (A : Type u) (B : Type v) :=
(lift : A → B)

/- Auxiliary class that contains the transitive closure of has_lift. -/
class has_lift_t (A : Type u) (B : Type v) :=
(lift : A → B)

class has_coe (A : Type u) (B : Type v) :=
(coe : A → B)

/- Auxiliary class that contains the transitive closure of has_coe. -/
class has_coe_t (A : Type u) (B : Type v) :=
(coe : A → B)

class has_coe_to_fun (A : Type u) : Type (max u (v+1)) :=
(F : Type v) (coe : A → F)

class has_coe_to_sort (A : Type u) : Type (max u (v+1)) :=
(S : Type v) (coe : A → S)

def lift {A : Type u} {B : Type v} [has_lift A B] : A → B :=
@has_lift.lift A B _

def lift_t {A : Type u} {B : Type v} [has_lift_t A B] : A → B :=
@has_lift_t.lift A B _

def coe_b {A : Type u} {B : Type v} [has_coe A B] : A → B :=
@has_coe.coe A B _

def coe_t {A : Type u} {B : Type v} [has_coe_t A B] : A → B :=
@has_coe_t.coe A B _

set_option pp.all true
def coe_fn_b {A : Type u} [has_coe_to_fun.{u v} A] : A → has_coe_to_fun.F.{u v} A :=
has_coe_to_fun.coe

/- User level coercion operators -/

def coe {A : Type u} {B : Type v} [has_lift_t A B] : A → B :=
lift_t

def coe_fn {A : Type u} [has_coe_to_fun.{u v} A] : A → has_coe_to_fun.F.{u v} A :=
has_coe_to_fun.coe

def coe_sort {A : Type u} [has_coe_to_sort.{u v} A] : A → has_coe_to_sort.S.{u v} A :=
has_coe_to_sort.coe

/- Notation -/

notation `↑`:max a:max := coe a

notation `⇑`:max a:max := coe_fn a

notation `↥`:max a:max := coe_sort a

universe variables u₁ u₂ u₃

/- Transitive closure for has_lift, has_coe, has_coe_to_fun -/

instance lift_trans {A : Type u₁} {B : Type u₂} {C : Type u₃} [has_lift A B] [has_lift_t B C] : has_lift_t A C :=
⟨λ a, lift_t (lift a : B)⟩

instance lift_base {A : Type u} {B : Type v} [has_lift A B] : has_lift_t A B :=
⟨lift⟩

instance coe_trans {A : Type u₁} {B : Type u₂} {C : Type u₃} [has_coe A B] [has_coe_t B C] : has_coe_t A C :=
⟨λ a, coe_t (coe_b a : B)⟩

instance coe_base {A : Type u} {B : Type v} [has_coe A B] : has_coe_t A B :=
⟨coe_b⟩

instance coe_fn_trans {A : Type u₁} {B : Type u₂} [has_lift_t A B] [has_coe_to_fun.{u₂ u₃} B] : has_coe_to_fun.{u₁ u₃} A :=
⟨has_coe_to_fun.F B, λ a, coe_fn (coe a)⟩

instance coe_sort_trans {A : Type u₁} {B : Type u₂} [has_lift_t A B] [has_coe_to_sort.{u₂ u₃} B] : has_coe_to_sort.{u₁ u₃} A :=
⟨has_coe_to_sort.S B, λ a, coe_sort (coe a)⟩

/- Every coercion is also a lift -/

instance coe_to_lift {A : Type u} {B : Type v} [has_coe_t A B] : has_lift_t A B :=
⟨coe_t⟩

/- Basic coercions -/

instance coe_bool_to_Prop : has_coe bool Prop :=
⟨λ b, b = tt⟩

instance coe_decidable_eq (b : bool) : decidable (coe b) :=
show decidable (b = tt), from bool.decidable_eq b tt

instance coe_subtype {A : Type u} {p : A → Prop} : has_coe {a // p a} A :=
⟨λ s, subtype.elt_of s⟩

/- Basic lifts -/

universe variables ua ua₁ ua₂ ub ub₁ ub₂

/- Remark: we can't use [has_lift_t A₂ A₁] since it will produce non-termination whenever a type class resolution
   problem does not have a solution. -/
instance lift_fn {A₁ : Type ua₁} {A₂ : Type ua₂} {B₁ : Type ub₁} {B₂ : Type ub₂} [has_lift A₂ A₁] [has_lift_t B₁ B₂] : has_lift (A₁ → B₁) (A₂ → B₂) :=
⟨λ f a, ↑(f ↑a)⟩

instance lift_fn_range {A : Type ua} {B₁ : Type ub₁} {B₂ : Type ub₂} [has_lift_t B₁ B₂] : has_lift (A → B₁) (A → B₂) :=
⟨λ f a, ↑(f a)⟩

instance lift_fn_dom {A₁ : Type ua₁} {A₂ : Type ua₂} {B : Type ub} [has_lift A₂ A₁] : has_lift (A₁ → B) (A₂ → B) :=
⟨λ f a, f ↑a⟩

instance lift_pair {A₁ : Type ua₁} {A₂ : Type ub₂} {B₁ : Type ub₁} {B₂ : Type ub₂} [has_lift_t A₁ A₂] [has_lift_t B₁ B₂] : has_lift (A₁ × B₁) (A₂ × B₂) :=
⟨λ p, prod.cases_on p (λ a b, (↑a, ↑b))⟩

instance lift_pair₁ {A₁ : Type ua₁} {A₂ : Type ua₂} {B : Type ub} [has_lift_t A₁ A₂] : has_lift (A₁ × B) (A₂ × B) :=
⟨λ p, prod.cases_on p (λ a b, (↑a, b))⟩

instance lift_pair₂ {A : Type ua} {B₁ : Type ub₁} {B₂ : Type ub₂} [has_lift_t B₁ B₂] : has_lift (A × B₁) (A × B₂) :=
⟨λ p, prod.cases_on p (λ a b, (a, ↑b))⟩

instance lift_list {A : Type u} {B : Type v} [has_lift_t A B] : has_lift (list A) (list B) :=
⟨λ l, list.map (@coe A B _) l⟩
