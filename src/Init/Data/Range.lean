/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Meta

namespace Std
-- We put `Range` in `Init` because we want the notation `[i:j]`  without importing `Std`
-- We don't put `Range` in the top-level namespace to avoid collisions with user defined types
structure Range where
  start : Nat := 0
  stop  : Nat
  step  : Nat := 1

namespace Range
universe u v

@[inline] protected def forIn {β : Type u} {m : Type u → Type v} [Monad m] (range : Range) (init : β) (f : Nat → β → m (ForInStep β)) : m β :=
  let rec @[specialize] loop (i : Nat) (j : Nat) (b : β) : m β := do
    if j ≥ range.stop then
      pure b
    else match i with
     | 0   => pure b
     | i+1 => match (← f j b) with
        | ForInStep.done b  => pure b
        | ForInStep.yield b => loop i (j + range.step) b
  loop range.stop range.start init

instance : ForIn m Range Nat where
  forIn := Range.forIn

@[inline] protected def forM {m : Type u → Type v} [Monad m] (range : Range) (f : Nat → m PUnit) : m PUnit :=
  let rec @[specialize] loop (i : Nat) (j : Nat) : m PUnit := do
    if j ≥ range.stop then
      pure ⟨⟩
    else match i with
     | 0   => pure ⟨⟩
     | i+1 => f j; loop i (j + range.step)
  loop range.stop range.start

instance : ForM m Range Nat where
  forM := Range.forM

syntax:max "[" ":" term "]" : term
syntax:max "[" term ":" term "]" : term
syntax:max "[" ":" term ":" term "]" : term
syntax:max "[" term ":" term ":" term "]" : term

macro_rules
  | `([ : $stop]) => `({ stop := $stop : Range })
  | `([ $start : $stop ]) => `({ start := $start, stop := $stop : Range })
  | `([ $start : $stop : $step ]) => `({ start := $start, stop := $stop, step := $step : Range })
  | `([ : $stop : $step ]) => `({ stop := $stop, step := $step : Range })

end Range
end Std
