import Init.System.IO
import Lean.Server

def main (n : List String) : IO UInt32 := do
i ← IO.stdin;
o ← IO.stdout;
e ← IO.stderr;
Lean.initSearchPath;
catch
  (Lean.Server.initAndRunServer i o)
  (fun err => e.putStrLn (toString err));
pure 0
