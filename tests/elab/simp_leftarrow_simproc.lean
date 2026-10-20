/-!
`←` on a simproc or simp extension should error instead of being silently ignored (#15197).
-/

/-- error: Invalid `←` modifier: Cannot be used on a simp extension -/
#guard_msgs in
example : True := by
  simp [← seval]

/-- error: Invalid `←` modifier: `Nat.reduceDvd` is a simproc -/
#guard_msgs in
example : True := by
  simp [← Nat.reduceDvd]
