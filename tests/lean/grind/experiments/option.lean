open Option

-- TODO: the following lemmas currently fail, but could be solved with some subset of the following attributes:
-- I haven't added them yet, because the nuclear option of `[grind cases]` is tempting, but a bit scary.

attribute [grind] Option.eq_none_of_isNone
attribute [grind] Option.toArray_eq_empty_iff
attribute [grind] Option.toList_eq_nil_iff

attribute [grind cases] Option

theorem toArray_eq_empty_iff {o : Option α} : o.toArray = #[] ↔ o = none := by
  grind

theorem toArray_eq_singleton_iff {o : Option α} : o.toArray = #[a] ↔ o = some a := by
  grind

theorem size_toArray_eq_zero_iff {o : Option α} :
    o.toArray.size = 0 ↔ o = none := by
  grind

theorem toList_eq_nil_iff {o : Option α} : o.toList = [] ↔ o = none := by
  grind

theorem toList_eq_singleton_iff {o : Option α} : o.toList = [a] ↔ o = some a := by
  grind

theorem length_toList_eq_zero_iff {o : Option α} :
    o.toList.length = 0 ↔ o = none := by
  grind

attribute [grind] Std.IdempotentOp -- Lots more of these!

example [Max α] [Std.IdempotentOp (α := α) max] {p : α → Bool} {o : Option α} :
    max (o.filter p) o = o := by grind

example [Max α] [Std.IdempotentOp (α := α) max] {o : Option α} {p : (a : α) → o = some a → Bool} :
    max (o.pfilter p) o = o := by grind

example [Max α] {o o' : Option α} : (max o o').isSome = (o.isSome || o'.isSome) := by grind

example [Max α] {o o' : Option (Option α)} : (max o o').join = max o.join o'.join := by grind
