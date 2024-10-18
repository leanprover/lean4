-- When the elaborator doesn't provide `CompletionInfo`, try to provide identifier completions.
-- As of when this test case was written, the elaborator did not provide `CompletionInfo` in these cases.

-- https://github.com/leanprover/lean4/issues/5172

inductive Direction where
  | up
  | right
  | down
  | left
deriving Repr

def angle (d: Direction) :=
  match d with
  | Direction. => 90
            --^ textDocument/completion
  | Direction.right => 0
  | Direction.down => 270
  | Direction.left => 180

-- Ensure that test is stable when changes to the `And` namespace are made.
structure CustomAnd (a b : Prop) : Prop where
  ha : a
  hb : b

example : p ∨ (q ∧ r) → CustomAnd (p ∨ q) (p ∨ r) := by
  intro h
  cases h with
  | inl hp => apply CustomAnd. (Or.intro_left q hp) (Or.intro_left r hp)
                            --^ textDocument/completion
  | inr hqr => apply CustomAnd.mk (Or.intro_right p hqr.left) (Or.intro_right p hqr.right)
