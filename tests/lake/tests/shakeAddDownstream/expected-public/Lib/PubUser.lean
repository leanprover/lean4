module

public import Lib.Leaf

/-! Reaches whatever `Lib.Leaf` imports publicly. -/

@[expose] public def pubUserVal : Nat := leafVal
