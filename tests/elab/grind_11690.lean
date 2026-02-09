/-!
# Test for issue #11690: grind should support dot notation on declarations

When using `grind only [foo.le]` where `foo.le` is dot notation applying
`LT.lt.le` to a theorem `foo`, grind should elaborate it as a term rather
than failing with "Unknown constant `foo.le`".
-/

class Preorder (α : Type) extends LE α, LT α where

theorem le_of_lt [Preorder α] {a b : α} (hab : a < b) : a ≤ b := sorry

variable [Preorder α]

def LT.lt.le := @le_of_lt

axiom α : Type
axiom a : α
axiom b : α
axiom bar : a < b

example : a ≤ b := bar.le  -- works (term elaboration)

#guard_msgs in
example : a ≤ b := by
  grind only [bar.le]
