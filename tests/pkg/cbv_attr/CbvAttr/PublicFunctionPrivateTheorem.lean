module

public def f5 (x : Nat) :=
  x + 1

@[reducible] public def redId (x : Nat) := x

@[cbv_eval] private theorem f5_spec : f5 x = redId x + 1 := rfl

/- works locally -/
example : f5 1 = 2 := by conv => lhs; cbv
