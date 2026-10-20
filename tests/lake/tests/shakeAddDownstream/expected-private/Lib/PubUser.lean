module

public import Lib.Leaf
import Lib.Init

/-! Reaches whatever `Lib.Leaf` imports publicly. -/

@[expose] public def pubUserVal : Nat := leafVal
