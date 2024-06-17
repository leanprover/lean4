@[deprecated]
theorem hi : True := .intro

set_option linter.deprecated false in
@[deprecated]
theorem hi_self : hi = hi := rfl

example : True := by
  simp [← hi_self, hi]
                   --^ collectDiagnostics
