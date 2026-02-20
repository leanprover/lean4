/--
error: Tactic `native_decide` evaluated that the proposition
  foldl (fun x1 x2 => x1 + x2) 0 #[1, 2, 3] 0 5 = 0
is false
-/
#guard_msgs in
theorem Array.foldl_broken : False := by
  let x := #[1,2,3].foldl (. + .) 0 (stop := 5)
  have : x = 6 := by rfl
  have : x = 0 := by native_decide -- must fail
  contradiction

/--
error: Tactic `native_decide` evaluated that the proposition
  Array.foldl (fun x1 x2 => x1 + x2) 0 #[1, 2, 3] 0 5 = 0
is false
-/
#guard_msgs in
example : #[1,2,3].foldl (. + .) 0 (stop := 5) = 0 := by
  native_decide -- must fail

example : #[1,2,3].foldl (. + .) 0 (stop := 5) = 6 := by
  native_decide
