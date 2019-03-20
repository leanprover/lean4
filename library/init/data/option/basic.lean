/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.core init.control.monad init.control.alternative init.coe
open decidable

universes u v

namespace option

def toMonad {m : Type → Type} [monad m] [alternative m] {A} : option A → m A
| none := failure
| (some a) := pure a

def getOrElse {α : Type u} : option α → α → α
| (some x) _ := x
| none     e := e

def get {α : Type u} [inhabited α] : option α → α
| (some x) := x
| none     := default α

def toBool {α : Type u} : option α → bool
| (some _) := tt
| none     := ff

def isSome {α : Type u} : option α → bool
| (some _) := tt
| none     := ff

def isNone {α : Type u} : option α → bool
| (some _) := ff
| none     := tt

@[inline] protected def bind {α : Type u} {β : Type v} : option α → (α → option β) → option β
| none     b := none
| (some a) b := b a

@[inline] protected def map {α β} (f : α → β) (o : option α) : option β :=
option.bind o (some ∘ f)

theorem mapId {α} : (option.map id : option α → option α) = id :=
funext (λo, match o with | none := rfl | some x := rfl)

instance : monad option :=
{pure := @some, bind := @option.bind, map := @option.map}

protected def orelse {α : Type u} : option α → option α → option α
| (some a) o         := some a
| none     (some a)  := some a
| none     none      := none

instance : alternative option :=
{ failure := @none,
  orelse  := @option.orelse,
  ..option.monad }

protected def lt {α : Type u} (r : α → α → Prop) : option α → option α → Prop
| none (some x)     := true
| (some x) (some y) := r x y
| _ _               := false

instance decidableRelLt {α : Type u} (r : α → α → Prop) [s : decidableRel r] : decidableRel (option.lt r)
| none     (some y) := isTrue  trivial
| (some x) (some y) := s x y
| (some x) none     := isFalse notFalse
| none     none     := isFalse notFalse

end option

instance (α : Type u) : inhabited (option α) :=
⟨none⟩

instance {α : Type u} [decidableEq α] : decidableEq (option α) :=
{decEq := λ a b, match a, b with
 | none,      none      := isTrue rfl
 | none,      (some v₂) := isFalse (λ h, option.noConfusion h)
 | (some v₁), none      := isFalse (λ h, option.noConfusion h)
 | (some v₁), (some v₂) :=
   match decEq v₁ v₂ with
   | (isTrue e)  := isTrue (congrArg (@some α) e)
   | (isFalse n) := isFalse (λ h, option.noConfusion h (λ e, absurd e n))}

instance {α : Type u} [hasLt α] : hasLt (option α) := ⟨option.lt (<)⟩
