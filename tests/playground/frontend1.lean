import init.lean.elaborator
open Lean

def main (xs : List String) : IO Unit :=
do contents ← IO.readTextFile xs.head;
   (env, messages) ← testFrontend contents xs.head;
   messages.toList.mfor $ fun msg => IO.println msg;
   pure ()
