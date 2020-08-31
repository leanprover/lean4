/-
Copyright (c) 2020 Wojciech Nawrocki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Wojciech Nawrocki
-/
import Init.System.IO
import Lean.Server

def main (n : List String) : IO UInt32 := do
i ← IO.getStdin;
o ← IO.getStdout;
e ← IO.getStderr;
Lean.initSearchPath;
catch
  (Lean.Server.initAndRunServer i o)
  (fun err => e.putStrLn (toString err));
pure 0
