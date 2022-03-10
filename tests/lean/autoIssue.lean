structure A :=
  x : Nat
  a' : x = 1 := by trivial

#check @A.a'

example (z : A) : z.x = 1 := by
  have := z.a'
  trace_state
  exact this

example (z : A) : z.x = 1 := by
  have := z.2
  trace_state
  exact this
