module
-- This file uses `#guard_msgs` to check which lemmas `grind` is using.
-- This may prove fragile, so remember it is okay to update the expected output if appropriate!
-- Hopefully these will act as regression tests against `grind` activating irrelevant lemmas.

section

variable [BEq α] {o₁ o₂ o₃ o₄ o₅ : Option α}

/--
info: Try this:
  grind only [=_
      Option.or_assoc,
    = Option.getD_or, = Option.or_some, = Option.some_beq_none, = Option.or_assoc, = Option.some_or]
-/
#guard_msgs in
example : ((o₁.or (o₂.or (some x))).or (o₄.or o₅) == none) = false := by grind?

/--
info: Try this:
  grind only [Option.max_none_right,
    Option.min_some_some, = Nat.min_def]
-/
#guard_msgs in
example : max (some 7) none = min (some 13) (some 7) := by grind?

/--
info: Try this:
  grind only [= Option.guard_apply]
-/
#guard_msgs in
example : Option.guard (· ≤ 7) 3 = some 3 := by grind?

/--
info: Try this:
  grind only [=
      Option.mem_bind_iff]
-/
#guard_msgs in
example {x : β} {o : Option α} {f : α → Option β} (h : a ∈ o) (h' : x ∈ f a) : x ∈ o.bind f := by grind?

end

open Option

theorem toList_toArray {o : Option α} : o.toArray.toList = o.toList := by
  grind

theorem toArray_toList {o : Option α} : o.toList.toArray = o.toArray := by
  grind

theorem size_toArray_eq_one_iff {o : Option α} :
    o.toArray.size = 1 ↔ o.isSome := by
  grind

theorem size_toArray_choice_eq_one [Nonempty α] : (choice α).toArray.size = 1 := by
  grind

theorem length_toList_eq_one_iff {o : Option α} :
    o.toList.length = 1 ↔ o.isSome := by
  grind

theorem length_toList_choice_eq_one [Nonempty α] : (choice α).toList.length = 1 := by
  grind

example : (default : Option α) = none := by grind

example (a : α) : Option.all q (guard p a) = (!p a || q a) := by grind

example (a : α) : Option.any q (guard p a) = (p a && q a) := by grind

example : (guard p a).or (guard q a) = guard (fun x => p x || q x) a := by grind
