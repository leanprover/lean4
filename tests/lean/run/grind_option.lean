-- This file uses `#guard_msgs` to check which lemmas `grind` is using.
-- This may prove fragile, so remember it is okay to update the expected output if appropriate!
-- Hopefully these will act as regression tests against `grind` activating irrelevant lemmas.

set_option grind.warning false

variable [BEq α] {o₁ o₂ o₃ o₄ o₅ : Option α}

/--
info: Try this: grind only [Option.or_some, Option.some_or, Option.or_assoc, Option.some_beq_none]
-/
#guard_msgs in
example : ((o₁.or (o₂.or (some x))).or (o₄.or o₅) == none) = false := by grind?

/-- info: Try this: grind only [= Nat.min_def, Option.max_some_none, Option.min_some_some] -/
#guard_msgs in
example : max (some 7) none = min (some 13) (some 7) := by grind?

/-- info: Try this: grind only [Option.guard_def] -/
#guard_msgs in
example : Option.guard (· ≤ 7) 3 = some 3 := by grind?

/-- info: Try this: grind only [Option.mem_bind_iff] -/
#guard_msgs in
example {x : β} {o : Option α} {f : α → Option β} (h : a ∈ o) (h' : x ∈ f a) : x ∈ o.bind f := by grind?
