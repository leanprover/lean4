set_option grind.warning false

variable [BEq α] {o₁ o₂ o₃ o₄ o₅ : Option α}

/--
info: Try this: grind only [Option.some_or, Option.or_some', Option.or_assoc, Option.some_beq_none, Option.none_beq_none]
-/
#guard_msgs in
example : ((o₁.or (o₂.or (some x))).or (o₄.or o₅) == none) = false := by grind?

/--
info: Try this: grind only [Option.max_none_none, Option.min_some_none, = Nat.min_def, Option.some_beq_none,
  Option.min_none_none, Option.max_some_none, Option.min_some_some, Option.none_beq_none]
-/
#guard_msgs in
example : max (some 7) none = min (some 13) (some 7) := by grind?

/--
info: Try this: grind only [Option.min_some_none, Option.some_beq_none, Option.guard_pos, Option.max_some_none]
-/
#guard_msgs in
example : Option.guard (· ≤ 7) 3 = some 3 := by grind? [Option.guard_pos]

-- reset_grind_attrs%

set_option trace.grind.ematch.pattern true
attribute [grind] Option.some_beq_none
set_option trace.grind.assert true
set_option trace.grind.ematch true
example : Option.guard (· ≤ 7) 3 = some 3 := by grind? [Option.guard_pos]
