/-! Test that the `zero` parameter in `Nat.caseStrongRecOn`, which was made computable
in https://github.com/leanprover/lean4/pull/12894, is not eagerly evaluated. -/

def foo (n : Nat) : Nat := Nat.caseStrongRecOn n (panic!"I shouldn't be run") fun n _ ↦ n

/-- info: 1 -/
#guard_msgs in
#eval foo 2
