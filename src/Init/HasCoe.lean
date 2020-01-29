/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/

/-
The Elaborator tries to insert coercions automatically.
Only instances of HasCoe type class are considered in the process.

Lean also provides a "lifting" operator: ↑a.
It uses all instances of HasLift type class.
Every HasCoe instance is also a HasLift instance.

We recommend users only use HasCoe for coercions that do not produce a lot
of ambiguity.

All coercions and lifts can be identified with the constant coe.

We use the HasCoeToFun type class for encoding coercions from
a Type to a Function space.

We use the HasCoeToSort type class for encoding coercions from
a Type to a sort.
-/
prelude
import Init.Data.List.Basic
universes u v

class HasLift (a : Sort u) (b : Sort v) :=
(lift : a → b)

/-- Auxiliary class that contains the transitive closure of HasLift. -/
class HasLiftT (a : Sort u) (b : Sort v) :=
(lift : a → b)

class HasCoe (a : Sort u) (b : Sort v) :=
(coe : a → b)

/-- Auxiliary class that contains the transitive closure of HasCoe. -/
class HasCoeT (a : Sort u) (b : Sort v) :=
(coe : a → b)

class HasCoeToFun (a : Sort u) : Sort (max u (v+1)) :=
(F : a → Sort v) (coe : ∀ x, F x)

class HasCoeToSort (a : Sort u) : Type (max u (v+1)) :=
(S : Sort v) (coe : a → S)

@[inline] def lift {a : Sort u} {b : Sort v} [HasLift a b] : a → b :=
@HasLift.lift a b _

@[inline] def liftT {a : Sort u} {b : Sort v} [HasLiftT a b] : a → b :=
@HasLiftT.lift a b _

@[inline] def oldCoeB {a : Sort u} {b : Sort v} [HasCoe a b] : a → b :=
@HasCoe.coe a b _

@[inline] def oldCoeT {a : Sort u} {b : Sort v} [HasCoeT a b] : a → b :=
@HasCoeT.coe a b _

@[inline] def oldCoeFnB {a : Sort u} [HasCoeToFun.{u, v} a] : ∀ (x : a), HasCoeToFun.F.{u, v} x :=
HasCoeToFun.coe

/- User Level coercion operators -/

@[reducible, inline] def oldCoe {a : Sort u} {b : Sort v} [HasLiftT a b] : a → b :=
liftT

@[reducible, inline] def oldCoeFn {a : Sort u} [HasCoeToFun.{u, v} a] : ∀ (x : a), HasCoeToFun.F.{u, v} x :=
HasCoeToFun.coe

@[reducible, inline] def oldCoeSort {a : Sort u} [HasCoeToSort.{u, v} a] : a → HasCoeToSort.S.{u, v} a :=
HasCoeToSort.coe

/- Notation -/

universes u₁ u₂ u₃

/- Transitive closure for HasLift, HasCoe, HasCoeToFun -/

namespace Legacy

instance liftTrans {a : Sort u₁} {b : Sort u₂} {c : Sort u₃} [HasLiftT b c] [HasLift a b] : HasLiftT a c :=
⟨fun x => liftT (lift x : b)⟩

instance liftRefl {a : Sort u} : HasLiftT a a :=
⟨id⟩

instance coeoeTrans {a : Sort u₁} {b : Sort u₂} {c : Sort u₃} [HasCoeT b c] [HasCoe a b] : HasCoeT a c :=
⟨fun x => oldCoeT (oldCoeB x : b)⟩

instance coeBase {a : Sort u} {b : Sort v} [HasCoe a b] : HasCoeT a b :=
⟨oldCoeB⟩

/- We add this instance directly into HasCoeT to avoid non-termination.

   Suppose coeOption had Type (HasCoe a (Option a)).
   Then, we can loop when searching a coercion from α to β (HasCoeT α β)
   1- coeTrans at (HasCoeT α β)
          (HasCoe α ?b₁) and (HasCoeT ?b₁ c)
   2- coeOption at (HasCoe α ?b₁)
          ?b₁ := Option α
   3- coeTrans at (HasCoeT (Option α) β)
          (HasCoe (Option α) ?b₂) and (HasCoeT ?b₂ β)
   4- coeOption at (HasCoe (Option α) ?b₂)
          ?b₂ := Option (Option α))
   ...
-/
instance oldCoeOption {a : Type u} : HasCoeT a (Option a) :=
⟨fun x => some x⟩

/- Auxiliary transitive closure for HasCoe which does not contain
   instances such as coeOption.

   They would produce non-termination when combined with coeFnTrans and coeSortTrans.
-/
class HasCoeTAux (a : Sort u) (b : Sort v) :=
(coe : a → b)

instance coeTransAux {a : Sort u₁} {b : Sort u₂} {c : Sort u₃} [HasCoeTAux b c] [HasCoe a b] : HasCoeTAux a c :=
⟨fun x => @HasCoeTAux.coe b c _ (oldCoeB x)⟩

instance coeBaseAux {a : Sort u} {b : Sort v} [HasCoe a b] : HasCoeTAux a b :=
⟨oldCoeB⟩

instance coeFnTrans {a : Sort u₁} {b : Sort u₂} [HasCoeToFun.{u₂, u₃} b] [HasCoeTAux a b] : HasCoeToFun.{u₁, u₃} a :=
{ F   := fun x => @HasCoeToFun.F.{u₂, u₃} b _ (@HasCoeTAux.coe a b _ x),
  coe := fun x => oldCoeFn (@HasCoeTAux.coe a b _ x) }

instance coeSortTrans {a : Sort u₁} {b : Sort u₂} [HasCoeToSort.{u₂, u₃} b] [HasCoeTAux a b] : HasCoeToSort.{u₁, u₃} a :=
{ S   := HasCoeToSort.S.{u₂, u₃} b,
  coe := fun x => oldCoeSort (@HasCoeTAux.coe a b _ x) }

/- Every coercion is also a lift -/

instance coeToLift {a : Sort u} {b : Sort v} [HasCoeT a b] : HasLiftT a b :=
⟨oldCoeT⟩

/- basic coercions -/

@[inline] instance coeBoolToProp : HasCoe Bool Prop :=
⟨fun y => y = true⟩

@[inline] instance coeDecidableEq (x : Bool) : Decidable (oldCoe x) :=
inferInstanceAs (Decidable (x = true))

instance coeSubtype {a : Sort u} {p : a → Prop} : HasCoe {x // p x} a :=
⟨Subtype.val⟩

/- basic lifts -/

universes ua ua₁ ua₂ ub ub₁ ub₂

/- Remark: we can't use [HasLiftT a₂ a₁] since it will produce non-termination whenever a type class resolution
   problem does not have a solution. -/
instance liftFn {a₁ : Sort ua₁} {a₂ : Sort ua₂} {b₁ : Sort ub₁} {b₂ : Sort ub₂} [HasLiftT b₁ b₂] [HasLift a₂ a₁] : HasLift (a₁ → b₁) (a₂ → b₂) :=
⟨fun f x => oldCoe (f (oldCoe x))⟩

instance liftFnRange {a : Sort ua} {b₁ : Sort ub₁} {b₂ : Sort ub₂} [HasLiftT b₁ b₂] : HasLift (a → b₁) (a → b₂) :=
⟨fun f x => oldCoe (f x)⟩

instance liftFnDom {a₁ : Sort ua₁} {a₂ : Sort ua₂} {b : Sort ub} [HasLift a₂ a₁] : HasLift (a₁ → b) (a₂ → b) :=
⟨fun f x => f (oldCoe x)⟩

instance liftPair {a₁ : Type ua₁} {a₂ : Type ub₂} {b₁ : Type ub₁} {b₂ : Type ub₂} [HasLiftT a₁ a₂] [HasLiftT b₁ b₂] : HasLift (a₁ × b₁) (a₂ × b₂) :=
⟨fun p => Prod.casesOn p (fun x y => (oldCoe x,  oldCoe y))⟩

instance liftPair₁ {a₁ : Type ua₁} {a₂ : Type ua₂} {b : Type ub} [HasLiftT a₁ a₂] : HasLift (a₁ × b) (a₂ × b) :=
⟨fun p => Prod.casesOn p (fun x y => (oldCoe x, y))⟩

instance liftPair₂ {a : Type ua} {b₁ : Type ub₁} {b₂ : Type ub₂} [HasLiftT b₁ b₂] : HasLift (a × b₁) (a × b₂) :=
⟨fun p => Prod.casesOn p (fun x y => (x,  oldCoe y))⟩

instance liftList {a : Type u} {b : Type v} [HasLiftT a b] : HasLift (List a) (List b) :=
⟨fun l => List.map (@oldCoe a b _) l⟩

end Legacy

instance oldCoeToLift {a : Sort u} {b : Sort v} [HasCoeT a b] : HasLiftT a b :=
⟨oldCoeT⟩
