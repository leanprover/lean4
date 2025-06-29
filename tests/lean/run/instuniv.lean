import Lean

open Lean

unsafe def tst : IO Unit :=
  withImportModules #[{module := `Init.Data.Array}] {} fun env =>
    match env.find? `Array.foldl with
    | some info => do
      IO.println (info.instantiateTypeLevelParams [levelZero, levelZero])
      IO.println (info.instantiateValueLevelParams! [levelZero, levelZero])
      IO.println (info.instantiateValueLevelParams! [levelZero])
    | none      => IO.println "Array.foldl not found"

#eval tst
