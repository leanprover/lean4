-- There should be no warning for `linter.unusedSimpArgs`
set_option linter.all false in
example : True := by simp [False]
