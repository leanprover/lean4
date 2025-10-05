import Lean

def Foo.ExampleDL := 42

elab "s3(" dl:ident ")" : term => do
  -- remove the `Lean.liftCommandElabM` to remove error below
  let _ ← Lean.liftCommandElabM (Lean.resolveGlobalConstNoOverload dl)
  return .const ``Nat []

#check s3(Foo.ExampleDL)

namespace Foo
-- "Unknown constant `ExampleDL`". Reproducible in https://live.lean-lang.org/
#check s3(ExampleDL)
