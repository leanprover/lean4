namespace Option

theorem eq_some_iff_get_eq' {o : Option α} {a : α} :
  o = some a ↔ ∃ h : o.isSome, Option.get _ h = a := by
  cases o; simp only [isSome_none, false_iff, reduceCtorEq]; intro h; cases h; contradiction
  simp [exists_prop]
