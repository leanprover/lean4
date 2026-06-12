module

import UserAttr.BlaAttr

/-! Middle module that plain-imports `UserAttr.BlaAttr`, used by `UserAttr.MetaUser` to set up the
`meta import` chain that triggers the regression in
https://github.com/leanprover/lean4/issues/13599. -/

@[expose] public section

def midVal : Nat := 17

end
