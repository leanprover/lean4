module

public def f6 (x : Nat) :=
  x + 1

private axiom myAx : x + 1 = f6 x

@[cbv_eval ←] public theorem f6_spec : x + 1 = f6 x := myAx

example : f6 1 = 2 := by conv => lhs; cbv
