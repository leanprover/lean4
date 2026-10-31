--^ textDocument/foldingRange
module

/-! Folding ranges of kind `proof` in a module, where public theorems are exported as axioms. -/

public def publicPropDef : True := by
  trivial

public theorem publicThm : True := by
  trivial

theorem privateThm : True := by
  trivial

public def publicDef : Nat := by
  exact 0
