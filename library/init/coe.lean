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
universes u v

class has_lift (a : Sort u) (b : Sort v) :=
(lift : a → b)

/-- Auxiliary class that contains the transitive closure of has_lift. -/
class has_lift_t (a : Sort u) (b : Sort v) :=
(lift : a → b)

class has_coe (a : Sort u) (b : Sort v) :=
(coe : a → b)

/-- Auxiliary class that contains the transitive closure of has_coe. -/
class has_coe_t (a : Sort u) (b : Sort v) :=
(coe : a → b)

class has_coe_to_fun (a : Sort u) : Sort (max u (v+1)) :=
(F : a → Sort v) (coe : Π x, F x)

class has_coe_to_sort (a : Sort u) : Type (max u (v+1)) :=
(S : Sort v) (coe : a → S)

def lift {a : Sort u} {b : Sort v} [has_lift a b] : a → b :=
@has_lift.lift a b _

def lift_t {a : Sort u} {b : Sort v} [has_lift_t a b] : a → b :=
@has_lift_t.lift a b _

def coe_b {a : Sort u} {b : Sort v} [has_coe a b] : a → b :=
@has_coe.coe a b _

def coe_t {a : Sort u} {b : Sort v} [has_coe_t a b] : a → b :=
@has_coe_t.coe a b _

def coe_fn_b {a : Sort u} [has_coe_to_fun.{u v} a] : Π x : a, has_coe_to_fun.F.{u v} x :=
has_coe_to_fun.coe

/- User level coercion operators -/

@[reducible] def coe {a : Sort u} {b : Sort v} [has_lift_t a b] : a → b :=
lift_t

@[reducible] def coe_fn {a : Sort u} [has_coe_to_fun.{u v} a] : Π x : a, has_coe_to_fun.F.{u v} x :=
has_coe_to_fun.coe

@[reducible] def coe_sort {a : Sort u} [has_coe_to_sort.{u v} a] : a → has_coe_to_sort.S.{u v} a :=
has_coe_to_sort.coe

/- Notation -/

notation `↑`:max x:max := coe x

notation `⇑`:max x:max := coe_fn x

notation `↥`:max x:max := coe_sort x

universes u₁ u₂ u₃

/- Transitive closure for has_lift, has_coe, has_coe_to_fun -/

instance lift_trans {a : Sort u₁} {b : Sort u₂} {c : Sort u₃} [has_lift a b] [has_lift_t b c] : has_lift_t a c :=
⟨λ x, lift_t (lift x : b)⟩

instance lift_base {a : Sort u} {b : Sort v} [has_lift a b] : has_lift_t a b :=
⟨lift⟩

instance coe_trans {a : Sort u₁} {b : Sort u₂} {c : Sort u₃} [has_coe a b] [has_coe_t b c] : has_coe_t a c :=
⟨λ x, coe_t (coe_b x : b)⟩

instance coe_base {a : Sort u} {b : Sort v} [has_coe a b] : has_coe_t a b :=
⟨coe_b⟩

/- We add this instance directly into has_coe_t to avoid non-termination.

   Suppose coe_option had type (has_coe a (option a)).
   Then, we can loop when searching a coercion from α to β (has_coe_t α β)
   1- coe_trans at (has_coe_t α β)
          (has_coe α ?b₁) and (has_coe_t ?b₁ c)
   2- coe_option at (has_coe α ?b₁)
          ?b₁ := option α
   3- coe_trans at (has_coe_t (option α) β)
          (has_coe (option α) ?b₂) and (has_coe_t ?b₂ β)
   4- coe_option at (has_coe (option α) ?b₂)
          ?b₂ := option (option α))
   ...
-/
instance coe_option {a : Type u} : has_coe_t a (option a) :=
⟨λ x, some x⟩

/- Auxiliary transitive closure for has_coe which does not contain
   instances such as coe_option.

   They would produce non-termination when combined with coe_fn_trans and coe_sort_trans.
-/
class has_coe_t_aux (a : Sort u) (b : Sort v) :=
(coe : a → b)

instance coe_trans_aux {a : Sort u₁} {b : Sort u₂} {c : Sort u₃} [has_coe a b] [has_coe_t_aux b c] : has_coe_t_aux a c :=
⟨λ x : a, @has_coe_t_aux.coe b c _ (coe_b x)⟩

instance coe_base_aux {a : Sort u} {b : Sort v} [has_coe a b] : has_coe_t_aux a b :=
⟨coe_b⟩

instance coe_fn_trans {a : Sort u₁} {b : Sort u₂} [has_coe_t_aux a b] [has_coe_to_fun.{u₂ u₃} b] : has_coe_to_fun.{u₁ u₃} a :=
{ F   := λ x, @has_coe_to_fun.F.{u₂ u₃} b _ (@has_coe_t_aux.coe a b _ x),
  coe := λ x, coe_fn (@has_coe_t_aux.coe a b _ x) }

instance coe_sort_trans {a : Sort u₁} {b : Sort u₂} [has_coe_t_aux a b] [has_coe_to_sort.{u₂ u₃} b] : has_coe_to_sort.{u₁ u₃} a :=
{ S   := has_coe_to_sort.S.{u₂ u₃} b,
  coe := λ x, coe_sort (@has_coe_t_aux.coe a b _ x) }

/- Every coercion is also a lift -/

instance coe_to_lift {a : Sort u} {b : Sort v} [has_coe_t a b] : has_lift_t a b :=
⟨coe_t⟩

/- basic coercions -/

instance coe_bool_to_Prop : has_coe bool Prop :=
⟨λ y, y = tt⟩

/- Tactics such as the simplifier only unfold reducible constants when checking whether two terms are definitionally
   equal or a term is a proposition. The motivation is performance.
   In particular, when simplifying `p -> q`, the tactic `simp` only visits `p` if it can establish that it is a proposition.
   Thus, we mark the following instance as @[reducible], otherwise `simp` will not visit `↑p` when simplifying `↑p -> q`.
-/
@[reducible] instance coe_sort_bool : has_coe_to_sort bool :=
⟨Prop, λ y, y = tt⟩

instance coe_decidable_eq (x : bool) : decidable (coe x) :=
show decidable (x = tt), from bool.decidable_eq x tt

instance coe_subtype {a : Sort u} {p : a → Prop} : has_coe {x // p x} a :=
⟨subtype.val⟩

/- basic lifts -/

universes ua ua₁ ua₂ ub ub₁ ub₂

/- Remark: we can't use [has_lift_t a₂ a₁] since it will produce non-termination whenever a type class resolution
   problem does not have a solution. -/
instance lift_fn {a₁ : Sort ua₁} {a₂ : Sort ua₂} {b₁ : Sort ub₁} {b₂ : Sort ub₂} [has_lift a₂ a₁] [has_lift_t b₁ b₂] : has_lift (a₁ → b₁) (a₂ → b₂) :=
⟨λ f x, ↑(f ↑x)⟩

instance lift_fn_range {a : Sort ua} {b₁ : Sort ub₁} {b₂ : Sort ub₂} [has_lift_t b₁ b₂] : has_lift (a → b₁) (a → b₂) :=
⟨λ f x, ↑(f x)⟩

instance lift_fn_dom {a₁ : Sort ua₁} {a₂ : Sort ua₂} {b : Sort ub} [has_lift a₂ a₁] : has_lift (a₁ → b) (a₂ → b) :=
⟨λ f x, f ↑x⟩

instance lift_pair {a₁ : Type ua₁} {a₂ : Type ub₂} {b₁ : Type ub₁} {b₂ : Type ub₂} [has_lift_t a₁ a₂] [has_lift_t b₁ b₂] : has_lift (a₁ × b₁) (a₂ × b₂) :=
⟨λ p, prod.cases_on p (λ x y, (↑x, ↑y))⟩

instance lift_pair₁ {a₁ : Type ua₁} {a₂ : Type ua₂} {b : Type ub} [has_lift_t a₁ a₂] : has_lift (a₁ × b) (a₂ × b) :=
⟨λ p, prod.cases_on p (λ x y, (↑x, y))⟩

instance lift_pair₂ {a : Type ua} {b₁ : Type ub₁} {b₂ : Type ub₂} [has_lift_t b₁ b₂] : has_lift (a × b₁) (a × b₂) :=
⟨λ p, prod.cases_on p (λ x y, (x, ↑y))⟩

instance lift_list {a : Type u} {b : Type v} [has_lift_t a b] : has_lift (list a) (list b) :=
⟨λ l, list.map (@coe a b _) l⟩
