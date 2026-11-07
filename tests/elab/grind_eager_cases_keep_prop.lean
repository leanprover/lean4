module

/-!
Eager `cases` on a new `Prop` hypothesis must keep the hypothesis itself.

`grind` applies `cases` eagerly to hypotheses introduced by `intros` and to asserted facts whose
type is marked `[grind cases eager]`. Previously, only the constructor fields survived in each
branch, so the proposition itself was never recorded as true.
-/

inductive P : Prop
  | a | b

attribute [grind cases eager] P

theorem mkP : P := .a

example : P := by
  grind [(mkP)]

example : P → ¬P → False := by
  grind

example : ¬P → P → False := by
  grind

inductive Good (n : Nat) : Prop
  | mk (h : 0 < n)

attribute [grind cases eager] Good

example (n : Nat) : Good n → Good n := by
  grind

example (n : Nat) : Good n → 0 < n := by
  grind

/-! Hypotheses already in the context are unaffected. -/

example (n : Nat) (h : Good n) : Good n := by
  grind

example (h : ¬P) (hp : P) : False := by
  grind
