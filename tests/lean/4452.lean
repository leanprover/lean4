def a := 1

@[deprecated "Don't use `hi`." (since := "1970-01-01")]
theorem hi : a = 1 := rfl

attribute [simp] hi

example (h : 1 = b) : a = b := by
  simp
  guard_target =ₛ 1 = b
  exact h

set_option linter.all true

example (h : 1 = b) : a = b := by
  simp[
    hi
  ]
  guard_target =ₛ 1 = b
  exact h

@[deprecated "Don't use `hi'`, either." (since := "1970-01-01")]
theorem hi' : True := .intro

example : True := by
  -- the warning is on `simp`
  simp [
    hi'  -- warning should be logged here
  ]
