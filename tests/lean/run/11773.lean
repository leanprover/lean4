/-! This is a regression test for an issue with the implemented_by of Array.foldlM -/

/--
error: Tactic `native_decide` evaluated that the proposition
  foldl (fun x1 x2 => x1 + x2) 0 #[1, 2, 3] 0 5 = 0
is false
-/
#guard_msgs in
theorem Array.foldl_broken : False := by
  let x := #[1,2,3].foldl (. + .) 0 (stop := 5)
  have : x = 6 := by rfl
  have : x = 0 := by native_decide
  contradiction

example : #[1,2,3].foldl (. + .) 0 (stop := 5) = 6 := by native_decide

/--
error: Tactic `native_decide` evaluated that the proposition
  foldl (fun x1 x2 => x1 + x2) 0 { data := #[1, 2, 3] } 0 5 = 0
is false
-/
#guard_msgs in
theorem ByteArray.foldl_broken : False := by
  let x := (ByteArray.mk #[1,2,3]).foldl (. + .) 0 (stop := 5)
  have : x = 6 := by rfl
  have : x = 0 := by native_decide
  grind

example : (ByteArray.mk #[1,2,3]).foldl (. + .) 0 (stop := 5) = 6 := by native_decide
