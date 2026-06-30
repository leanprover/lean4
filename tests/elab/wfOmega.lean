/-! A wf recursive definition that needs omega to work -/

def foo (n : Nat) :=
  if h : n < 99 then 0 else foo (n - 99)
