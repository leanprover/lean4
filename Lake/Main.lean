/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner, Sebastian Ullrich, Mac Malone
-/
import Lake.Cli
import Lake.SearchPath

def main (args : List String) : IO UInt32 := do
  try
    Lake.setupLeanSearchPath
    Lake.cli args
    pure 0
  catch e =>
    IO.eprintln <| "error: " ++ toString e -- avoid "uncaught exception: ..."
    pure 1
