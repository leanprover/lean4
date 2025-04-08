/--
warning: Binder uses 'instDecidableEqOfLawfulBEq', consider adding a [DecidableEq ...] instance assumption to avoid this
note: this linter can be disabled with `set_option linter.decEqOfLawful false`
-/
#guard_msgs in
example [BEq α] [LawfulBEq α] (x : α) : if x ∈ [] then True else True := by
  simp

set_option linter.beqOfDecEq true

/--
warning: Binder uses 'instBEqOfDecidableEq', consider adding [BEq ...] and [LawfulBEq ...] instance assumptions to avoid this
note: this linter can be disabled with `set_option linter.beqOfDecEq false`
-/
#guard_msgs in
example [DecidableEq α] (x : α) : [].count x = 0 := by
  simp
