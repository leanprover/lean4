import Lean

/-!
The lookup caches of imported-constant views are freed together with their import set, so
repeatedly importing modules in one process does not accumulate them.
-/

open Lean

unsafe def importAndLookup : IO Unit :=
  withImportModules #[{ module := `Init }] {} fun env => do
    unless (env.find? ``Nat.add).isSome do
      throw <| IO.userError "lookup of `Nat.add` failed"
    unless (env.find? `noSuchConstant).isNone do
      throw <| IO.userError "lookup of `noSuchConstant` succeeded"
    unless (env.getModuleIdxFor? ``Nat.add).isSome do
      throw <| IO.userError "module index of `Nat.add` missing"

/-- info: true -/
#guard_msgs in
#eval show IO Bool from do
  let before ← LookupCache.numLive
  for _ in [0:5] do
    unsafe importAndLookup
  return (← LookupCache.numLive) == before
