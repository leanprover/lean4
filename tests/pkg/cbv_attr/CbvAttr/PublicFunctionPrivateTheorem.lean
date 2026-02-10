module

set_option cbv.warning false

@[cbv_opaque] public def f5 (x : Nat) :=
  x + 1

@[cbv_eval] private theorem f5_spec : f5 x = x + 1 := rfl

/- works locally -/
example : f5 1 = 2 := by conv => lhs; cbv
