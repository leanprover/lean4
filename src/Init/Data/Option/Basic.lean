/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Core
import Init.Control.Basic
import Init.Coe

namespace Option

def toMonad [Monad m] [Alternative m] : Option α → m α
  | none     => failure
  | some a   => pure a

@[macroInline] def getD : Option α → α → α
  | some x, _ => x
  | none,   e => e

@[inline] def toBool : Option α → Bool
  | some _ => true
  | none   => false

@[inline] def isSome : Option α → Bool
  | some _ => true
  | none   => false

@[inline] def isNone : Option α → Bool
  | some _ => false
  | none   => true

@[inline] protected def bind : Option α → (α → Option β) → Option β
  | none,   b => none
  | some a, b => b a

@[inline] protected def map (f : α → β) (o : Option α) : Option β :=
  Option.bind o (some ∘ f)

theorem mapId : (Option.map id : Option α → Option α) = id :=
  funext (fun o => match o with | none => rfl | some x => rfl)

instance : Monad Option := {
  pure := some
  bind := Option.bind
  map  := Option.map
}

@[inline] protected def filter (p : α → Bool) : Option α → Option α
  | some a => if p a then some a else none
  | none   => none

@[inline] protected def all (p : α → Bool) : Option α → Bool
  | some a => p a
  | none   => true

@[inline] protected def any (p : α → Bool) : Option α → Bool
  | some a => p a
  | none   => false

@[macroInline] protected def orElse : Option α → Option α → Option α
  | some a, _ => some a
  | none,   b => b

/- Remark: when using the polymorphic notation `a <|> b` is not a `[macroInline]`.
   Thus, `a <|> b` will make `Option.orelse` to behave like it was marked as `[inline]`. -/
instance : Alternative Option := {
  failure := none,
  orElse  := Option.orElse
}

@[inline] protected def lt (r : α → α → Prop) : Option α → Option α → Prop
  | none, some x     => True
  | some x,   some y => r x y
  | _, _             => False

instance (r : α → α → Prop) [s : DecidableRel r] : DecidableRel (Option.lt r)
  | none,   some y => isTrue  trivial
  | some x, some y => s x y
  | some x, none   => isFalse notFalse
  | none,   none   => isFalse notFalse

end Option

instance [DecidableEq α] : DecidableEq (Option α) := fun a b =>
  match a, b with
  | none,      none      => isTrue rfl
  | none,      (some v₂) => isFalse (fun h => Option.noConfusion h)
  | (some v₁), none      => isFalse (fun h => Option.noConfusion h)
  | (some v₁), (some v₂) =>
    match decEq v₁ v₂ with
    | (isTrue e)  => isTrue (congrArg (@some α) e)
    | (isFalse n) => isFalse (fun h => Option.noConfusion h (fun e => absurd e n))

instance [BEq α] : BEq (Option α) where
  beq
    | none,      none      => true
    | none,      (some v₂) => false
    | (some v₁), none      => false
    | (some v₁), (some v₂) => v₁ == v₂

instance [HasLess α] : HasLess (Option α) := {
  Less := Option.lt (· < ·)
}
