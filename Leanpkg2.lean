/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner, Sebastian Ullrich, Mac Malone
-/
import Leanpkg2.Cli

def main (args : List String) : IO UInt32 := do
  try
    let (cmd, outerArgs, innerArgs) ← Leanpkg2.splitCmdlineArgs args
    Leanpkg2.cli cmd outerArgs innerArgs
    pure 0
  catch e =>
    IO.eprintln e  -- avoid "uncaught exception: ..."
    pure 1
