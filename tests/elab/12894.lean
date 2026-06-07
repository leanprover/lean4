def foo (n : Nat) : Nat := Nat.caseStrongRecOn n (panic!"I shouldn't be run") fun n _ ↦ n

/-- info: 1 -/
#guard_msgs in
#eval foo 2
