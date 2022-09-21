import Lean

open Lean Meta

#eval id (α := MetaM Unit) do
  modifyEnv fun env => env.addExtraName `auxDecl1
  return ()

def foo := 42
