/--
info: Try these:
• simp +arith
• simp +arith +decide
---
error: `simp_arith` has been deprecated. It was a shorthand for `simp +arith +decide`, but most of the time, `+decide` was redundant since simprocs have been implemented.
-/
#guard_msgs in
example : x + 2 = 1 + 1 + x := by
  simp_arith

/--
info: Try these:
• simp +arith [h, id] at h₂
• simp +arith +decide [h, id] at h₂
---
error: `simp_arith` has been deprecated. It was a shorthand for `simp +arith +decide`, but most of the time, `+decide` was redundant since simprocs have been implemented.
-/
#guard_msgs in
example (h : x = y) (h₂ : y + 2 = 1 + 1 + x) : True := by
  simp_arith [h, id] at h₂

/--
info: Try these:
• simp! +arith [h, id] at h₂
• simp! +arith +decide [h, id] at h₂
---
error: `simp_arith!` has been deprecated. It was a shorthand for `simp! +arith +decide`, but most of the time, `+decide` was redundant since simprocs have been implemented.
-/
#guard_msgs in
example (h : x = y) (h₂ : y + 2 = 1 + 1 + x) : True := by
  simp_arith! [h, id] at h₂


/--
info: Try these:
• simp_all +arith
• simp_all +arith +decide
---
error: `simp_all_arith` has been deprecated. It was a shorthand for `simp_all +arith +decide`, but most of the time, `+decide` was redundant since simprocs have been implemented.
-/
#guard_msgs in
example (h : x = y) (h₂ : y + 2 = 1 + 1 + x) : True := by
  simp_all_arith

/--
info: Try these:
• simp_all! +arith
• simp_all! +arith +decide
---
error: `simp_all_arith!` has been deprecated. It was a shorthand for `simp_all! +arith +decide`, but most of the time, `+decide` was redundant since simprocs have been implemented.
-/
#guard_msgs in
example (h : x = y) (h₂ : y + 2 = 1 + 1 + x) : True := by
  simp_all_arith!
