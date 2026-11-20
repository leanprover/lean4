module

public import CollectAxioms.SorryCode

/-! A definition calling imported code that contains `sorry`, for `CollectAxioms.EvalSorry`. -/

public def viaSorryCode (b : Bool) : Nat := sorryInCode b
