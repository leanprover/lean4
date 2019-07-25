import init.lean.elaborator
open Lean

def main (xs : List String) : IO Unit :=
do path ← IO.getEnv "LEAN_PATH";
   IO.println path;
   contents ← IO.readTextFile xs.head;
   (env, messages) ← testFrontend contents xs.head;
   messages.toList.mfor $ fun msg => IO.println msg;
   pure ()
