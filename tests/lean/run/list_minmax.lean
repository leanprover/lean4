/-! ### min? -/

/--
info: none
-/
#guard_msgs(info) in #eval ([]: List Nat).min?

/--
info: some 1
-/
#guard_msgs(info) in #eval [1].min?

/--
info: some 1
-/
#guard_msgs(info) in #eval [1, 4, 2, 10, 6].min?

/--
info: some (-10)
-/
#guard_msgs(info) in #eval [-1, -4, -2, -10, -6].min?

/-! ### min -/

/--
error: unsolved goals
⊢ False
-/
#guard_msgs(error) in #eval [].min (by simp)

/--
info: 1
-/
#guard_msgs(info) in #eval [1].min (by decide)

/--
info: 1
-/
#guard_msgs(info) in #eval [1, 4, 2, 10, 6].min (by decide)

/--
info: -10
-/
#guard_msgs(info) in #eval [-1, -4, -2, -10, -6].min (by decide)

/-! ### max? -/

/--
info: none
-/
#guard_msgs(info) in #eval ([]: List Nat).max?

/--
info: some 4
-/
#guard_msgs(info) in #eval [4].max?

/--
info: some 10
-/
#guard_msgs(info) in #eval [1, 4, 2, 10, 6].max?

/--
info: some (-1)
-/
#guard_msgs(info) in #eval [-1, -4, -2, -10, -6].max?

/-! ### max -/

/--
error: unsolved goals
⊢ False
-/
#guard_msgs(error) in #eval [].max (by simp)

/--
info: 4
-/
#guard_msgs(info) in #eval [4].max (by decide)

/--
info: 10
-/
#guard_msgs(info) in #eval [1, 4, 2, 10, 6].max (by decide)

/--
info: -1
-/
#guard_msgs(info) in #eval [-1, -4, -2, -10, -6].max (by decide)
