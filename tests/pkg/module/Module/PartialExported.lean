module

public import Lean

/-!
Producer half of a regression test: a `partial` definition of type `False`, added directly through
`addDecl`. Since the module is not `@[expose]`d, the definition is exported as an axiom stub, which
must stay marked unsafe.
-/

open Lean

public section

run_meta do
  let name := `partialFalse
  addDecl (.mutualDefnDecl [{
    name
    levelParams := []
    type := mkConst ``False
    value := mkConst name
    hints := .opaque
    safety := .partial
  }])

end
