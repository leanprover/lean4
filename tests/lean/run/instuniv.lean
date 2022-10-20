import Lean

open Lean

unsafe def tst : IO Unit :=
  withImportModules [{module := `Init.Data.Array}] {} 0 fun env =>
    match env.find? `Array.foldl with
    | some info => do
      IO.println (info.instantiateTypeLevelParams [levelZero, levelZero]).toOption.get!
      IO.println (info.instantiateValueLevelParams [levelZero, levelZero]).toOption.get!
    | none      => IO.println "Array.foldl not found"

#eval tst
