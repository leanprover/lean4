import init.lean.elaborator
open Lean

def main (xs : List String) : IO Unit :=
do initSearchPath "../../library:.";
   -- path ← IO.getEnv "LEAN_PATH";
   -- IO.println path;
   contents ← IO.readTextFile xs.head;
   (env, messages) ← Elab.testFrontend contents xs.head;
   messages.toList.mfor $ fun msg => IO.println msg;
   pure ()
