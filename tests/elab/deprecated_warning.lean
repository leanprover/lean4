/-- warning: declaration uses `sorry` -/
#guard_msgs in
@[deprecated " " (since := "2020-01-01")]
theorem test : 3 = 5 := sorry

@[deprecated " " (since := "2020-01-01")]
theorem test2 : 3 = 5 := by
  grind [test]

@[deprecated " " (since := "2020-01-01")]
theorem test3 : 3 = 5 := by
  as_aux_lemma =>
    exact test
