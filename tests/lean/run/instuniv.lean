import Init.Lean
open Lean

def tst : IO Unit :=
do env ← importModules [`Init.Data.Array.Default];
   match env.find `Array.foldl with
   | some info => do
     IO.println (info.instantiateTypeUnivParams [Level.zero, Level.zero]);
     IO.println (info.instantiateValueUnivParams [Level.zero, Level.zero]);
     pure ()
   | none      => IO.println ("Array.foldl not found");
   pure ()

#eval tst
