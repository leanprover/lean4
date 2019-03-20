/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/

/-
The elaborator tries to insert coercions automatically.
Only instances of hasCoe type class are considered in the process.

Lean also provides a "lifting" operator: ↑a.
It uses all instances of hasLift type class.
Every hasCoe instance is also a hasLift instance.

We recommend users only use hasCoe for coercions that do not produce a lot
of ambiguity.

All coercions and lifts can be identified with the constant coe.

We use the hasCoeToFun type class for encoding coercions from
a type to a function space.

We use the hasCoeToSort type class for encoding coercions from
a type to a sort.
-/
prelude
import init.data.list.basic
universes u v

class hasLift (a : Sort u) (b : Sort v) :=
(lift : a → b)

/-- Auxiliary class that contains the transitive closure of hasLift. -/
class hasLiftT (a : Sort u) (b : Sort v) :=
(lift : a → b)

class hasCoe (a : Sort u) (b : Sort v) :=
(coe : a → b)

/-- Auxiliary class that contains the transitive closure of hasCoe. -/
class hasCoeT (a : Sort u) (b : Sort v) :=
(coe : a → b)

class hasCoeToFun (a : Sort u) : Sort (max u (v+1)) :=
(F : a → Sort v) (coe : Π x, F x)

class hasCoeToSort (a : Sort u) : Type (max u (v+1)) :=
(S : Sort v) (coe : a → S)

@[inline] def lift {a : Sort u} {b : Sort v} [hasLift a b] : a → b :=
@hasLift.lift a b _

@[inline] def liftT {a : Sort u} {b : Sort v} [hasLiftT a b] : a → b :=
@hasLiftT.lift a b _

@[inline] def coeB {a : Sort u} {b : Sort v} [hasCoe a b] : a → b :=
@hasCoe.coe a b _

@[inline] def coeT {a : Sort u} {b : Sort v} [hasCoeT a b] : a → b :=
@hasCoeT.coe a b _

@[inline] def coeFnB {a : Sort u} [hasCoeToFun.{u v} a] : Π x : a, hasCoeToFun.F.{u v} x :=
hasCoeToFun.coe

/- User level coercion operators -/

@[reducible, inline] def coe {a : Sort u} {b : Sort v} [hasLiftT a b] : a → b :=
liftT

@[reducible, inline] def coeFn {a : Sort u} [hasCoeToFun.{u v} a] : Π x : a, hasCoeToFun.F.{u v} x :=
hasCoeToFun.coe

@[reducible, inline] def coeSort {a : Sort u} [hasCoeToSort.{u v} a] : a → hasCoeToSort.S.{u v} a :=
hasCoeToSort.coe

/- Notation -/

notation `↑`:max x:max := coe x

notation `⇑`:max x:max := coeFn x

notation `↥`:max x:max := coeSort x

universes u₁ u₂ u₃

/- Transitive closure for hasLift, hasCoe, hasCoeToFun -/

instance liftTrans {a : Sort u₁} {b : Sort u₂} {c : Sort u₃} [hasLift a b] [hasLiftT b c] : hasLiftT a c :=
⟨λ x, liftT (lift x : b)⟩

instance liftRefl {a : Sort u} : hasLiftT a a :=
⟨id⟩

instance coeTrans {a : Sort u₁} {b : Sort u₂} {c : Sort u₃} [hasCoe a b] [hasCoeT b c] : hasCoeT a c :=
⟨λ x, coeT (coeB x : b)⟩

instance coeBase {a : Sort u} {b : Sort v} [hasCoe a b] : hasCoeT a b :=
⟨coeB⟩

/- We add this instance directly into hasCoeT to avoid non-termination.

   Suppose coeOption had type (hasCoe a (option a)).
   Then, we can loop when searching a coercion from α to β (hasCoeT α β)
   1- coeTrans at (hasCoeT α β)
          (hasCoe α ?b₁) and (hasCoeT ?b₁ c)
   2- coeOption at (hasCoe α ?b₁)
          ?b₁ := option α
   3- coeTrans at (hasCoeT (option α) β)
          (hasCoe (option α) ?b₂) and (hasCoeT ?b₂ β)
   4- coeOption at (hasCoe (option α) ?b₂)
          ?b₂ := option (option α))
   ...
-/
instance coeOption {a : Type u} : hasCoeT a (option a) :=
⟨λ x, some x⟩

/- Auxiliary transitive closure for hasCoe which does not contain
   instances such as coeOption.

   They would produce non-termination when combined with coeFnTrans and coeSortTrans.
-/
class hasCoeTAux (a : Sort u) (b : Sort v) :=
(coe : a → b)

instance coeTransAux {a : Sort u₁} {b : Sort u₂} {c : Sort u₃} [hasCoe a b] [hasCoeTAux b c] : hasCoeTAux a c :=
⟨λ x : a, @hasCoeTAux.coe b c _ (coeB x)⟩

instance coeBaseAux {a : Sort u} {b : Sort v} [hasCoe a b] : hasCoeTAux a b :=
⟨coeB⟩

instance coeFnTrans {a : Sort u₁} {b : Sort u₂} [hasCoeTAux a b] [hasCoeToFun.{u₂ u₃} b] : hasCoeToFun.{u₁ u₃} a :=
{ F   := λ x, @hasCoeToFun.F.{u₂ u₃} b _ (@hasCoeTAux.coe a b _ x),
  coe := λ x, coeFn (@hasCoeTAux.coe a b _ x) }

instance coeSortTrans {a : Sort u₁} {b : Sort u₂} [hasCoeTAux a b] [hasCoeToSort.{u₂ u₃} b] : hasCoeToSort.{u₁ u₃} a :=
{ S   := hasCoeToSort.S.{u₂ u₃} b,
  coe := λ x, coeSort (@hasCoeTAux.coe a b _ x) }

/- Every coercion is also a lift -/

instance coeToLift {a : Sort u} {b : Sort v} [hasCoeT a b] : hasLiftT a b :=
⟨coeT⟩

/- basic coercions -/

instance coeBoolToProp : hasCoe bool Prop :=
⟨λ y, y = tt⟩

/- Tactics such as the simplifier only unfold reducible constants when checking whether two terms are definitionally
   equal or a term is a proposition. The motivation is performance.
   In particular, when simplifying `p -> q`, the tactic `simp` only visits `p` if it can establish that it is a proposition.
   Thus, we mark the following instance as @[reducible], otherwise `simp` will not visit `↑p` when simplifying `↑p -> q`.
-/
@[reducible] instance coeSortBool : hasCoeToSort bool :=
⟨Prop, λ y, y = tt⟩

instance coeDecidableEq (x : bool) : decidable (coe x) :=
show decidable (x = tt), from decEq x tt

instance coeSubtype {a : Sort u} {p : a → Prop} : hasCoe {x // p x} a :=
⟨subtype.val⟩

/- basic lifts -/

universes ua ua₁ ua₂ ub ub₁ ub₂

/- Remark: we can't use [hasLiftT a₂ a₁] since it will produce non-termination whenever a type class resolution
   problem does not have a solution. -/
instance liftFn {a₁ : Sort ua₁} {a₂ : Sort ua₂} {b₁ : Sort ub₁} {b₂ : Sort ub₂} [hasLift a₂ a₁] [hasLiftT b₁ b₂] : hasLift (a₁ → b₁) (a₂ → b₂) :=
⟨λ f x, ↑(f ↑x)⟩

instance liftFnRange {a : Sort ua} {b₁ : Sort ub₁} {b₂ : Sort ub₂} [hasLiftT b₁ b₂] : hasLift (a → b₁) (a → b₂) :=
⟨λ f x, ↑(f x)⟩

instance liftFnDom {a₁ : Sort ua₁} {a₂ : Sort ua₂} {b : Sort ub} [hasLift a₂ a₁] : hasLift (a₁ → b) (a₂ → b) :=
⟨λ f x, f ↑x⟩

instance liftPair {a₁ : Type ua₁} {a₂ : Type ub₂} {b₁ : Type ub₁} {b₂ : Type ub₂} [hasLiftT a₁ a₂] [hasLiftT b₁ b₂] : hasLift (a₁ × b₁) (a₂ × b₂) :=
⟨λ p, prod.casesOn p (λ x y, (↑x, ↑y))⟩

instance liftPair₁ {a₁ : Type ua₁} {a₂ : Type ua₂} {b : Type ub} [hasLiftT a₁ a₂] : hasLift (a₁ × b) (a₂ × b) :=
⟨λ p, prod.casesOn p (λ x y, (↑x, y))⟩

instance liftPair₂ {a : Type ua} {b₁ : Type ub₁} {b₂ : Type ub₂} [hasLiftT b₁ b₂] : hasLift (a × b₁) (a × b₂) :=
⟨λ p, prod.casesOn p (λ x y, (x, ↑y))⟩

instance liftList {a : Type u} {b : Type v} [hasLiftT a b] : hasLift (list a) (list b) :=
⟨λ l, list.map (@coe a b _) l⟩
