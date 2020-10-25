/-
Copyright (c) 2020 Wojciech Nawrocki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Wojciech Nawrocki
-/
import Init.System.IO
import Lean.Server

def main (n : List String) : IO UInt32 := do
  let i ← IO.getStdin
  let o ← IO.getStdout
  let e ← IO.getStderr
  Lean.initSearchPath
  try
    Lean.Server.initAndRunServer i o
  catch err =>
    e.putStrLn (toString err)
  pure 0
