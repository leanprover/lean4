/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
module

prelude
public import Init.Core
public import Init.Control.MonadAttach
public import Init.WFExtrinsicFix
import Init.While

set_option linter.missingDocs true

@[expose] public section

namespace Lean

/-!
# Well-founded `Repeat` type for verified `repeat`/`while` loops

This module provides a `Repeat` type that serves as an alternative to `Loop` for `repeat`/`while`
loops. Unlike `Loop`, which uses `partial` recursion, `Repeat` is implemented using
`WellFounded.extrinsicFix` and `MonadAttach`, enabling verified reasoning about loop programs.
-/

/-- A type for `repeat`/`while` loops that supports well-founded reasoning via `extrinsicFix`. -/
inductive Repeat where
  /-- Creates a `Repeat` value. -/
  | mk

/--
The step relation for well-founded recursion in `Repeat.forIn`.
Relates `b'` to `b` when `f () b` can plausibly return `ForInStep.yield b'`,
as witnessed by `MonadAttach.CanReturn`.
-/
def Repeat.IsPlausibleStep {β : Type u} {m : Type u → Type v} [Monad m] [MonadAttach m]
    (f : Unit → β → m (ForInStep β)) : β → β → Prop :=
  fun b' b => MonadAttach.CanReturn (f () b) (ForInStep.yield b')

/-- Iterates the body `f` using well-founded recursion via `extrinsicFix`. -/
@[inline]
def Repeat.forIn {β : Type u} {m : Type u → Type v} [Monad m] [MonadAttach m]
    (_ : Repeat) (init : β) (f : Unit → β → m (ForInStep β)) : m β :=
  haveI : Nonempty β := ⟨init⟩
  WellFounded.extrinsicFix (Repeat.IsPlausibleStep f) (a := init) fun b recur => do
    match ← MonadAttach.attach (f () b) with
      | ⟨ForInStep.done b, _⟩ => pure b
      | ⟨ForInStep.yield b, h⟩ => recur b h

instance [Monad m] [MonadAttach m] : ForIn m Repeat Unit where
  forIn := Repeat.forIn

end Lean
