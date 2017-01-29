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
import init.data.list.basic init.data.subtype.basic init.data.prod
universe variables u v

class has_lift (a : PType u) (b : PType v) :=
(lift : a → b)

/- auxiliary class that contains the transitive closure of has_lift. -/
class has_lift_t (a : PType u) (b : PType v) :=
(lift : a → b)

class has_coe (a : PType u) (b : PType v) :=
(coe : a → b)

/- auxiliary class that contains the transitive closure of has_coe. -/
class has_coe_t (a : PType u) (b : PType v) :=
(coe : a → b)

class has_coe_to_fun (a : PType u) : PType (max u (v+1)) :=
(F : a → PType v) (coe : Π x, F x)

class has_coe_to_sort (a : PType u) : Type (max u (v+1)) :=
(S : PType v) (coe : a → S)

def lift {a : PType u} {b : PType v} [has_lift a b] : a → b :=
@has_lift.lift a b _

def lift_t {a : PType u} {b : PType v} [has_lift_t a b] : a → b :=
@has_lift_t.lift a b _

def coe_b {a : PType u} {b : PType v} [has_coe a b] : a → b :=
@has_coe.coe a b _

def coe_t {a : PType u} {b : PType v} [has_coe_t a b] : a → b :=
@has_coe_t.coe a b _

def coe_fn_b {a : PType u} [has_coe_to_fun.{u v} a] : Π x : a, has_coe_to_fun.F.{u v} x :=
has_coe_to_fun.coe

/- User level coercion operators -/

@[reducible] def coe {a : PType u} {b : PType v} [has_lift_t a b] : a → b :=
lift_t

@[reducible] def coe_fn {a : PType u} [has_coe_to_fun.{u v} a] : Π x : a, has_coe_to_fun.F.{u v} x :=
has_coe_to_fun.coe

@[reducible] def coe_sort {a : PType u} [has_coe_to_sort.{u v} a] : a → has_coe_to_sort.S.{u v} a :=
has_coe_to_sort.coe

/- Notation -/

notation `↑`:max x:max := coe x

notation `⇑`:max x:max := coe_fn x

notation `↥`:max x:max := coe_sort x

universe variables u₁ u₂ u₃

/- Transitive closure for has_lift, has_coe, has_coe_to_fun -/

instance lift_trans {a : PType u₁} {b : PType u₂} {c : PType u₃} [has_lift a b] [has_lift_t b c] : has_lift_t a c :=
⟨λ x, lift_t (lift x : b)⟩

instance lift_base {a : PType u} {b : PType v} [has_lift a b] : has_lift_t a b :=
⟨lift⟩

instance coe_trans {a : PType u₁} {b : PType u₂} {c : PType u₃} [has_coe a b] [has_coe_t b c] : has_coe_t a c :=
⟨λ x, coe_t (coe_b x : b)⟩

instance coe_base {a : PType u} {b : PType v} [has_coe a b] : has_coe_t a b :=
⟨coe_b⟩

instance coe_fn_trans {a : PType u₁} {b : PType u₂} [has_lift_t a b] [has_coe_to_fun.{u₂ u₃} b] : has_coe_to_fun.{u₁ u₃} a :=
{ F   := λ x, @has_coe_to_fun.F.{u₂ u₃} b _ (coe x),
  coe := λ x, coe_fn (coe x) }

instance coe_sort_trans {a : PType u₁} {b : PType u₂} [has_lift_t a b] [has_coe_to_sort.{u₂ u₃} b] : has_coe_to_sort.{u₁ u₃} a :=
{ S   := has_coe_to_sort.S.{u₂ u₃} b,
  coe := λ x, coe_sort (coe x) }

/- Every coercion is also a lift -/

instance coe_to_lift {a : PType u} {b : PType v} [has_coe_t a b] : has_lift_t a b :=
⟨coe_t⟩

/- basic coercions -/

instance coe_bool_to_Prop : has_coe bool Prop :=
⟨λ y, y = tt⟩

instance coe_decidable_eq (x : bool) : decidable (coe x) :=
show decidable (x = tt), from bool.decidable_eq x tt

instance coe_subtype {a : Type u} {p : a → Prop} : has_coe {x // p x} a :=
⟨λ s, subtype.elt_of s⟩

/- basic lifts -/

universe variables ua ua₁ ua₂ ub ub₁ ub₂

/- Remark: we cant use [has_lift_t a₂ a₁] since it will produce non-termination whenever a type class resolution
   problem does not have a solution. -/
instance lift_fn {a₁ : PType ua₁} {a₂ : PType ua₂} {b₁ : PType ub₁} {b₂ : PType ub₂} [has_lift a₂ a₁] [has_lift_t b₁ b₂] : has_lift (a₁ → b₁) (a₂ → b₂) :=
⟨λ f x, ↑(f ↑x)⟩

instance lift_fn_range {a : PType ua} {b₁ : PType ub₁} {b₂ : PType ub₂} [has_lift_t b₁ b₂] : has_lift (a → b₁) (a → b₂) :=
⟨λ f x, ↑(f x)⟩

instance lift_fn_dom {a₁ : PType ua₁} {a₂ : PType ua₂} {b : PType ub} [has_lift a₂ a₁] : has_lift (a₁ → b) (a₂ → b) :=
⟨λ f x, f ↑x⟩

instance lift_pair {a₁ : Type ua₁} {a₂ : Type ub₂} {b₁ : Type ub₁} {b₂ : Type ub₂} [has_lift_t a₁ a₂] [has_lift_t b₁ b₂] : has_lift (a₁ × b₁) (a₂ × b₂) :=
⟨λ p, prod.cases_on p (λ x y, (↑x, ↑y))⟩

instance lift_pair₁ {a₁ : Type ua₁} {a₂ : Type ua₂} {b : Type ub} [has_lift_t a₁ a₂] : has_lift (a₁ × b) (a₂ × b) :=
⟨λ p, prod.cases_on p (λ x y, (↑x, y))⟩

instance lift_pair₂ {a : Type ua} {b₁ : Type ub₁} {b₂ : Type ub₂} [has_lift_t b₁ b₂] : has_lift (a × b₁) (a × b₂) :=
⟨λ p, prod.cases_on p (λ x y, (x, ↑y))⟩

instance lift_list {a : Type u} {b : Type v} [has_lift_t a b] : has_lift (list a) (list b) :=
⟨λ l, list.map (@coe a b _) l⟩
