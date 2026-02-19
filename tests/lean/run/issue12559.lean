/--
warning: This simp argument is unused:
  False

Hint: Omit it from the simp argument list.
  simp ̵[̵F̵a̵l̵s̵e̵]̵

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
-/
#guard_msgs in
example : True := by simp [False]

-- The `linter.all` option also controls the `linter.unusedSimpArgs` linter.
set_option linter.all false in
example : True := by simp [False]
