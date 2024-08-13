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

instance : Membership Nat Range where
  mem r i := r.start ≤ i ∧ i < r.stop

namespace Range
universe u v

@[inline] protected def forIn {β : Type u} {m : Type u → Type v} [Monad m] (range : Range) (init : β) (f : Nat → β → m (ForInStep β)) : m β :=
  -- pass `stop` and `step` separately so the `range` object can be eliminated through inlining
  let rec @[specialize] loop (fuel i stop step : Nat) (b : β) : m β := do
    if i ≥ stop then
      return b
    else match fuel with
     | 0   => pure b
     | fuel+1 => match (← f i b) with
        | ForInStep.done b  => pure b
        | ForInStep.yield b => loop fuel (i + step) stop step b
  loop range.stop range.start range.stop range.step init

instance : ForIn m Range Nat where
  forIn := Range.forIn

@[inline] protected def forIn' {β : Type u} {m : Type u → Type v} [Monad m] (range : Range) (init : β) (f : (i : Nat) → i ∈ range → β → m (ForInStep β)) : m β :=
  let rec @[specialize] loop (start stop step : Nat) (f : (i : Nat) → start ≤ i ∧ i < stop → β → m (ForInStep β)) (fuel i : Nat) (hl : start ≤ i) (b : β) : m β := do
    if hu : i < stop then
      match fuel with
      | 0   => pure b
      | fuel+1 => match (← f i ⟨hl, hu⟩ b) with
         | ForInStep.done b  => pure b
         | ForInStep.yield b => loop start stop step f fuel (i + step) (Nat.le_trans hl (Nat.le_add_right ..)) b
    else
      return b
  loop range.start range.stop range.step f range.stop range.start (Nat.le_refl ..) init

instance : ForIn' m Range Nat inferInstance where
  forIn' := Range.forIn'

@[inline] protected def forM {m : Type u → Type v} [Monad m] (range : Range) (f : Nat → m PUnit) : m PUnit :=
  let rec @[specialize] loop (fuel i stop step : Nat) : m PUnit := do
    if i ≥ stop then
      pure ⟨⟩
    else match fuel with
     | 0   => pure ⟨⟩
     | fuel+1 => f i; loop fuel (i + step) stop step
  loop range.stop range.start range.stop range.step

instance : ForM m Range Nat where
  forM := Range.forM

syntax:max "[" withoutPosition(":" term) "]" : term
syntax:max "[" withoutPosition(term ":" term) "]" : term
syntax:max "[" withoutPosition(":" term ":" term) "]" : term
syntax:max "[" withoutPosition(term ":" term ":" term) "]" : term

macro_rules
  | `([ : $stop]) => `({ stop := $stop : Range })
  | `([ $start : $stop ]) => `({ start := $start, stop := $stop : Range })
  | `([ $start : $stop : $step ]) => `({ start := $start, stop := $stop, step := $step : Range })
  | `([ : $stop : $step ]) => `({ stop := $stop, step := $step : Range })

end Range
end Std

theorem Membership.mem.upper {i : Nat} {r : Std.Range} (h : i ∈ r) : i < r.stop := h.2

theorem Membership.mem.lower {i : Nat} {r : Std.Range} (h : i ∈ r) : r.start ≤ i := h.1

theorem Membership.get_elem_helper {i n : Nat} {r : Std.Range} (h₁ : i ∈ r) (h₂ : r.stop = n) :
    i < n := h₂ ▸ h₁.2

macro_rules
  | `(tactic| get_elem_tactic_trivial) => `(tactic| apply Membership.get_elem_helper; assumption; rfl)
