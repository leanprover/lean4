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
# Slots of an exception postcondition

`EPostSlot ε Pred EPred` locates the slot for exceptions of type `ε` inside an exception
postcondition of type `EPred`, and `EPostSlot.set` fills that slot. The `throws` clause of a
`def` contract builds its exception postcondition with it: for
`ExceptT ε₁ (ExceptT ε₂ (StateM σ))` and a clause on `ε₂`, the term `EPostSlot.set R ⊥`
simplifies to `(⊥, R, estack⟨⟩)`.

Instance search dispatches on the exception type in the manner of `MonadExceptOf`: an
unconstrained `ε` lands in the outermost slot.
-/

variable {ε : Type u} {ε' : Type u'} {Pred : Type v} {Pred' : Type v'} {EPred : Type w}

/-- Locates the slot for exceptions of type `ε` inside an exception postcondition of type
`EPred`. The slot holds assertions of type `ε → Pred`. -/
class EPostSlot (ε : Type u) (Pred : outParam (Type v)) (EPred : Type w) where
  /-- Fills the `ε` slot of `epost` with `R`. Example: `set R (R₁, R₂) = (R₁, R)` for `ε` in
  the second slot. -/
  set (R : ε → Pred) (epost : EPred) : EPred

/-- A bare exception postcondition such as `Except ε`'s `ε → Prop` is its own slot. -/
instance instEPostSlotFun : EPostSlot ε Pred (ε → Pred) where
  set R _ := R

/-- The slot at the head of an exception postcondition stack. -/
instance instEPostSlotHead : EPostSlot ε Pred ((ε → Pred) × EPred) where
  set R e := (R, e.2)

/-- A slot in the tail of an exception postcondition stack. The head instance is tried first,
so an unconstrained `ε` lands in the outermost slot. -/
instance (priority := low) instEPostSlotTail [EPostSlot ε Pred EPred] :
    EPostSlot ε Pred ((ε' → Pred') × EPred) where
  set R e := (e.1, EPostSlot.set R e.2)

/-- Unfolds `set` at a bare exception postcondition. -/
theorem EPostSlot.set_fun (R : ε → Pred) (e : ε → Pred) :
    EPostSlot.set R e = R := rfl

/-- Unfolds `set` at the head slot of a stack. -/
theorem EPostSlot.set_head (R : ε → Pred) (e : (ε → Pred) × EPred) :
    EPostSlot.set R e = (R, e.2) := rfl

/-- Unfolds `set` at a slot in the tail of a stack. -/
theorem EPostSlot.set_tail [EPostSlot ε Pred EPred] (R : ε → Pred)
    (e : (ε' → Pred') × EPred) :
    EPostSlot.set R e = (e.1, EPostSlot.set R e.2) := rfl

end Std.WP
