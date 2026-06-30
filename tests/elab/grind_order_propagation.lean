/-!
Test propagation rules for `grind order`
-/

example (p q : Prop) : ((0 : Rat) < (1 : Rat) → p)
    → ¬ p ∨ q
    → ¬ p ∨ ¬q
    → False
   := by
  grind -linarith (splits := 0)

example (p q : Prop) : ((0 : Rat) ≤ (1 : Rat) → p)
    → ¬ p ∨ q
    → ¬ p ∨ ¬q
    → False
   := by
  grind -linarith (splits := 0)

example (p q s : Prop) : (if (0 : Rat) < (1 : Rat) then p else s)
    → ¬ p ∨ q
    → ¬ p ∨ ¬q
    → False
   := by
  grind -linarith (splits := 0)

example (p q s : Prop) : (if (0 : Rat) ≤ (0 : Rat) then p else s)
    → ¬ p ∨ q
    → ¬ p ∨ ¬q
    → False
   := by
  grind -linarith (splits := 0)

example (p q s : Prop) : (if (0 : Rat) > (1 : Rat) then s else p)
    → ¬ p ∨ q
    → ¬ p ∨ ¬q
    → False
   := by
  grind -linarith (splits := 0)

example (p q s : Prop) : (if (0 : Rat) >= (1 : Rat) then s else p)
    → ¬ p ∨ q
    → ¬ p ∨ ¬q
    → False
   := by
  grind -linarith (splits := 0)

-----
example (p q : Prop) (a : Rat) : (a < a + 1 → p)
    → ¬ p ∨ q
    → ¬ p ∨ ¬q
    → False
   := by
  grind -linarith (splits := 0)

example (p q : Prop) (a : Rat) : (a ≤ a → p)
    → ¬ p ∨ q
    → ¬ p ∨ ¬q
    → False
   := by
  grind -linarith (splits := 0)

example (p q s : Prop) (a : Rat) : (if a < a + 1 then p else s)
    → ¬ p ∨ q
    → ¬ p ∨ ¬q
    → False
   := by
  grind -linarith (splits := 0)

example (p q s : Prop) (a : Rat) : (if a ≤ a then p else s)
    → ¬ p ∨ q
    → ¬ p ∨ ¬q
    → False
   := by
  grind -linarith (splits := 0)

example (p q s : Prop) (a : Rat) : (if a > a + 1 then s else p)
    → ¬ p ∨ q
    → ¬ p ∨ ¬q
    → False
   := by
  grind -linarith (splits := 0)

example (p q s : Prop) (a : Rat) : (if a >= a + 1 then s else p)
    → ¬ p ∨ q
    → ¬ p ∨ ¬q
    → False
   := by
  grind -linarith (splits := 0)

-----

example [LE α] [Std.IsPreorder α] [DecidableLE α] (a : α) (p q s : Prop)
    : (if a ≤ a then p else s)
    → ¬ p ∨ q
    → ¬ p ∨ ¬q
    → False
   := by
  grind (splits := 0)

example [LE α] [LT α] [Std.LawfulOrderLT α] [Std.IsPreorder α] [DecidableLT α] (a : α) (p q s : Prop)
    : (if a < a then s else p)
    → ¬ p ∨ q
    → ¬ p ∨ ¬q
    → False
   := by
  grind (splits := 0)
