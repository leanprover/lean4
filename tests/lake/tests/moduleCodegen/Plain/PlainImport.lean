module

import Test.A

/-!
A module that generates code during its own elaboration can plainly import one that postpones its
code generation: it reads the signatures it needs from the import's `.ir.sig`.
-/

public def plainImport : Nat := twice 10
