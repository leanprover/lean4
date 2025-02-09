prelude
import Lean.AddDecl

open Lean

set_option debug.skipKernelTC true

def buildSyntheticEnv : Lean.CoreM Unit := do
  for i in [0:100000] do
    let name := s!"Long.And.Hopefully.Unique.Name.foo{i}".toName
    addDecl <| Declaration.opaqueDecl {
      name := name
      levelParams := []
      type := .const `Nat []
      value := .const `Nat.zero []
      isUnsafe := false
      all := [name]
    }
    addDocString name "A synthetic doc-string"

#eval buildSyntheticEnv

-- This will be quite a bit slower than the equivalent in a file that imports all of these decls,
-- since we can pre-compute information about those imports.
-- It still serves as a useful benchmark, though.
#eval Long.And.Hopefully.Unique.Name.foo
