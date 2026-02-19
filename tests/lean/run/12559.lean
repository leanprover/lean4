/-!
  # Make `linter.all` option also control the `linter.unusedSimpArgs` linter

  https://github.com/leanprover/lean4/issues/12559 -/

section

set_option linter.unusedSimpArgs true

/--
warning: This simp argument is unused:
  False

Hint: Omit it from the simp argument list.
  simp ̵[̵F̵a̵l̵s̵e̵]̵

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
-/
#guard_msgs in
example : True := by simp [False]

end

section

set_option linter.all true

/--
warning: This simp argument is unused:
  False

Hint: Omit it from the simp argument list.
  simp ̵[̵F̵a̵l̵s̵e̵]̵

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
-/
#guard_msgs in
example : True := by simp [False]

set_option linter.all false in
example : True := by simp [False]

end
