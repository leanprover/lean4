import Std.Do
import Std.Tactic.Do

/-!
Regression test for #13691: tactics that pattern-match on `MGoal.target`
(`mconstructor`, `mleft`, `mright`) failed inside `mhave` because the inner
goal's target carried hypothesis-naming metadata. The related round trip
`mrevert h; mintro h; mspecialize h` failed for the symmetric reason inside
`Revert`.
-/

open Std.Do

example (P : SPred [Int]) : P ⊢ₛ P ∧ P := by
  mintro hp
  mhave h : spred(P ∧ P) := by
    mconstructor
    · mexact hp
    · mexact hp
  mexact h

example (P : SPred [Int]) : P ⊢ₛ P ∨ P := by
  mintro hp
  mhave h : spred(P ∨ P) := by
    mleft
    mexact hp
  mexact h

example (P : SPred [Int]) : P ⊢ₛ P ∨ P := by
  mintro hp
  mhave h : spred(P ∨ P) := by
    mright
    mexact hp
  mexact h

example (P Q : SPred [Int]) : P ⊢ₛ (P → Q) → Q := by
  mintro HP HPQ
  mrevert HPQ
  mintro HPQ
  mspecialize HPQ HP
  mexact HPQ
