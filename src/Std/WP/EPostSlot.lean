/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
module

prelude
public import Std.WP.Assertion
public import Std.WP.EStack
universe u u' v v' w
@[expose] public section

set_option linter.missingDocs true

namespace Std.WP

/-!
# Slots of the exception postconditions

`EPostSlot EPosts ε EPred` locates the slot for exceptions of type `ε` inside exception
postconditions of type `EPosts`, and `EPostSlot.set` fills that slot. The `throws` clause of a
`def` contract builds its exception postconditions with it: for
`ExceptT ε₁ (ExceptT ε₂ (StateM σ))` and a clause on `ε₂`, the term `EPostSlot.set R ⊥`
simplifies to `(⊥, R, estack⟨⟩)`.

Instance search dispatches on the exception type in the manner of `MonadExceptOf`: an
unconstrained `ε` lands in the outermost slot.
-/

variable {ε : Type u} {ε' : Type u'} {EPred : Type v} {EPred' : Type v'} {EPosts : Type w}

/-- Locates the slot for exceptions of type `ε` inside exception postconditions of type
`EPosts`. The slot holds assertions of type `ε → EPred`. -/
class EPostSlot (EPosts : Type w) (ε : Type u) (EPred : outParam (Type v)) where
  /-- Fills the `ε` slot of `eposts` with `R`. Example: `set R (R₁, R₂) = (R₁, R)` for `ε` in
  the second slot. -/
  set (R : ε → EPred) (eposts : EPosts) : EPosts

/-- A bare exception postcondition such as `Except ε`'s `ε → Prop` is its own slot. -/
instance instEPostSlotFun : EPostSlot (ε → EPred) ε EPred where
  set R _ := R

/-- The slot at the head of an exception postcondition stack. -/
instance instEPostSlotHead : EPostSlot ((ε → EPred) × EPosts) ε EPred where
  set R eposts := (R, eposts.2)

/-- A slot in the tail of an exception postcondition stack. The head instance is tried first,
so an unconstrained `ε` lands in the outermost slot. -/
instance (priority := low) instEPostSlotTail [EPostSlot EPosts ε EPred] :
    EPostSlot ((ε' → EPred') × EPosts) ε EPred where
  set R eposts := (eposts.1, EPostSlot.set R eposts.2)

/-- Unfolds `set` at a bare exception postcondition. -/
theorem EPostSlot.set_fun (R : ε → EPred) (eposts : ε → EPred) :
    EPostSlot.set R eposts = R := rfl

/-- Unfolds `set` at the head slot of a stack. -/
theorem EPostSlot.set_head (R : ε → EPred) (eposts : (ε → EPred) × EPosts) :
    EPostSlot.set R eposts = (R, eposts.2) := rfl

/-- Unfolds `set` at a slot in the tail of a stack. -/
theorem EPostSlot.set_tail [EPostSlot EPosts ε EPred] (R : ε → EPred)
    (eposts : (ε' → EPred') × EPosts) :
    EPostSlot.set R eposts = (eposts.1, EPostSlot.set R eposts.2) := rfl

end Std.WP
