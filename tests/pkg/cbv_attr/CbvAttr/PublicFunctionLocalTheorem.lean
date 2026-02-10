module

set_option cbv.warning false

@[cbv_opaque] public def f2 (x : Nat) :=
  x + 1

private axiom myAx :  f2 x = x + 1

@[local cbv_eval] public theorem f2_spec : f2 x = x + 1 := myAx

example : f2 1 = 2 := by conv => lhs; cbv
