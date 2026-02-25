module

set_option cbv.warning false

@[cbv_opaque] public def f1 (x : Nat) :=
  x + 1

private axiom myAx :  f1 x = x + 1

@[cbv_eval] public theorem f1_spec : f1 x = x + 1 := myAx

example : f1 1 = 2 := by conv => lhs; cbv
