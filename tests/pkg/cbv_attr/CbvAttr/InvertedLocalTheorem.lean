module

public def f7 (x : Nat) :=
  x + 1

private axiom myAx : x + 1 = f7 x

@[local cbv_eval ←] public theorem f7_spec : x + 1 = f7 x := myAx

example : f7 1 = 2 := by conv => lhs; cbv
