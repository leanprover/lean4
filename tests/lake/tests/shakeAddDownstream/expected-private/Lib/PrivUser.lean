module

import Lib.Leaf
import Lib.Init

/-! Reaches the public imports of `Lib.Leaf`, but only privately. -/

public def privUserVal : Nat := leafVal
