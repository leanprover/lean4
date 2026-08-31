module
public import Lib.C

public def valueC' : Nat := 34

@[csimp]
public theorem valueC_eq_valueC' : valueC = valueC' := by
  rfl
