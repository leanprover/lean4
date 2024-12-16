/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Meta
import Init.Omega

namespace Std
-- We put `Range` in `Init` because we want the notation `[i:j]`  without importing `Std`
-- We don't put `Range` in the top-level namespace to avoid collisions with user defined types
structure Range where
  start : Nat := 0
  stop  : Nat
  step  : Nat := 1
  step_pos : 0 < step

instance : Membership Nat Range where
  mem r i := r.start ≤ i ∧ i < r.stop ∧ (i - r.start) % r.step = 0

namespace Range
universe u v

/-- The number of elements in the range. -/
def size (r : Range) : Nat := (r.stop - r.start + r.step - 1) / r.step

@[inline] protected def forIn' [Monad m] (range : Range) (init : β)
    (f : (i : Nat) → i ∈ range → β → m (ForInStep β)) : m β :=
  let rec @[specialize] loop (b : β) (i : Nat)
      (hs : (i - range.start) % range.step = 0) (hl : range.start ≤ i := by omega) : m β := do
    if h : i < range.stop then
      match (← f i ⟨hl, by omega, hs⟩ b) with
      | .done b  => pure b
      | .yield b =>
        have := range.step_pos
        loop b (i + range.step) (by rwa [Nat.add_comm, Nat.add_sub_assoc hl, Nat.add_mod_left])
    else
      pure b
  have := range.step_pos
  loop init range.start (by simp)

instance : ForIn' m Range Nat inferInstance where
  forIn' := Range.forIn'

-- No separate `ForIn` instance is required because it can be derived from `ForIn'`.

@[inline] protected def forM [Monad m] (range : Range) (f : Nat → m PUnit) : m PUnit :=
  let rec @[specialize] loop (i : Nat): m PUnit := do
    if i < range.stop then
      f i
      have := range.step_pos
      loop (i + range.step)
    else
      pure ⟨⟩
  have := range.step_pos
  loop range.start

instance : ForM m Range Nat where
  forM := Range.forM

syntax:max "[" withoutPosition(":" term) "]" : term
syntax:max "[" withoutPosition(term ":" term) "]" : term
syntax:max "[" withoutPosition(":" term ":" term) "]" : term
syntax:max "[" withoutPosition(term ":" term ":" term) "]" : term

macro_rules
  | `([ : $stop]) => `({ stop := $stop, step_pos := Nat.zero_lt_one : Range })
  | `([ $start : $stop ]) => `({ start := $start, stop := $stop, step_pos := Nat.zero_lt_one : Range })
  | `([ $start : $stop : $step ]) => `({ start := $start, stop := $stop, step := $step, step_pos := by decide : Range })
  | `([ : $stop : $step ]) => `({ stop := $stop, step := $step, step_pos := by decide : Range })

end Range
end Std

theorem Membership.mem.upper {i : Nat} {r : Std.Range} (h : i ∈ r) : i < r.stop := h.2.1

theorem Membership.mem.lower {i : Nat} {r : Std.Range} (h : i ∈ r) : r.start ≤ i := h.1

theorem Membership.mem.step {i : Nat} {r : Std.Range} (h : i ∈ r) : (i - r.start) % r.step = 0 := h.2.2

theorem Membership.get_elem_helper {i n : Nat} {r : Std.Range} (h₁ : i ∈ r) (h₂ : r.stop = n) :
    i < n := h₂ ▸ h₁.2.1

macro_rules
  | `(tactic| get_elem_tactic_trivial) => `(tactic| apply Membership.get_elem_helper; assumption; rfl)
