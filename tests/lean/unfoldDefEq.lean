def Wrapper (n : Nat) : Type × Type :=
  (Fin n, Fin n)

def SomeProperty {n} (x : Fin n) : Prop :=
  True

example (x : (Wrapper n).1) (h : SomeProperty x) : True := by
  unfold Wrapper at x
  trace_state
  simp at x
  trace_state
  sorry

example (x : (Wrapper n).1) (h : SomeProperty x) : True := by
  simp [Wrapper] at x
  trace_state
  sorry
