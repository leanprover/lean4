/-!
# `simp?`-suggested names conflicting with auxiliary declarations

https://github.com/leanprover/lean4/issues/6706

This test ensures that "unresolved" names provided by `simp?` do not conflict with local auxiliary
declarations.
-/

def P := True
theorem N.A.B : P := trivial
/-- info: Try this: simp only [N.A.B] -/
#guard_msgs in
theorem N.X.A.B : P := by
  simp? [N.A.B]

/-- info: Try this: simp only [_root_.N.A.B] -/
#guard_msgs in
theorem A : P :=
  let rec N.A.B := ()
  by simp? [_root_.N.A.B]
where B := ()
