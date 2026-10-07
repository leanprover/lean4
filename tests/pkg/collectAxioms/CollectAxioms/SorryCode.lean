module

/-! A definition whose compiled code contains `sorry`, for `CollectAxioms.EvalSorry`. -/

/-- warning: declaration uses `sorry` -/
#guard_msgs in
public def sorryInCode (b : Bool) : Nat := if b then sorry else 1
