module
public import Lean
import LocalElab.Lib -- NO `public`

local elab "myZero" : term => pure myZeroExpr
