import Lean
open Lean

unsafe def tst : IO Unit :=
withImportModules [{module := `Init.Data.Array}] 0 fun env => do
   match env.find? `Array.foldl with
   | some info => do
     IO.println (info.instantiateTypeLevelParams [levelZero, levelZero]);
     IO.println (info.instantiateValueLevelParams [levelZero, levelZero]);
     pure ()
   | none      => IO.println ("Array.foldl not found")

#eval tst
