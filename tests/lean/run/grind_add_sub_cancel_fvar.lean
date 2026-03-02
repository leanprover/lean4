import Lean

/-!
Regression test: `grind` on nested Nat subtraction chains.

After `simp only [Goal, loop]`, the goal becomes:
```
post (s₁ + s₂ - s₂ + s₂ - s₂ + ⋯ + s₂ - s₂) s₂
```
with `n` nested `(+ s₂ - s₂)` operations. Grind handles each Nat subtraction by
generating a `natCast_sub` fact, processed inside-out. The i-th fact has expression
size O(i). Before persistent caches were added, the preprocessing steps
`markNestedSubsingletons` and `canonImpl` used fresh per-call caches (traversing
all O(i) subexpressions each time), giving O(n²) total work.

This test checks that the scaling from n=25 to n=100 (4x) is at most 10x in wall-clock
time, which passes for ≤ O(n^1.7) but fails for O(n²) (which would give ~16x).
-/

def loop : Nat → (Nat → Nat → Prop) → (Nat → Nat → Prop)
  | 0, post => post
  | n+1, post => fun s₁ s₂ => loop n post (s₁ + s₂ - s₂) s₂
def Goal (n : Nat) : Prop := ∀ post s₁ s₂, post s₁ s₂ → loop n post s₁ s₂

set_option maxRecDepth 10000
set_option maxHeartbeats 10000000

open Lean Elab Command in
elab "#test_grind_scaling" : command => do
  let solveAt (n : Nat) : CommandElabM Nat := do
    let start ← IO.monoNanosNow
    elabCommand (← `(command|
      example : Goal $(Syntax.mkNumLit (toString n)) := by intros; simp only [Goal, loop]; grind
    ))
    let stop ← IO.monoNanosNow
    return stop - start
  let t_small ← solveAt 25
  let t_large ← solveAt 100
  let ratio := t_large.toFloat / t_small.toFloat
  -- Linear: expect ~4x for 4x problem size. Quadratic: would be ~16x.
  -- Use 10x as threshold (generous for noise, catches quadratic).
  if ratio > 10.0 then
    throwError "grind preprocessing scaling regression: 100/25 time ratio is {ratio}x (expected < 10x for linear scaling)"

#test_grind_scaling
