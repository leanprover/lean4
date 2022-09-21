import Misc.Foo
import Lean

open Lean Meta

#eval id (α := MetaM Unit) do
  assert! (← getEnv).getModuleIdxFor? ``foo == (← getEnv).getModuleIdxFor? `auxDecl1
  IO.println <| (← getEnv).getModuleIdxFor? ``Lean.Environment
  IO.println <| (← getEnv).getModuleIdxFor? ``foo
  IO.println <| (← getEnv).getModuleIdxFor? `auxDecl1
  IO.println "worked"
