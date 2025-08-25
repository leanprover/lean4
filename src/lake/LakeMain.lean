/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner, Sebastian Ullrich, Mac Malone
-/
module

prelude
public import Init.System.IO
import Lake.DSL -- registers builtins
import Lake.CLI.Main

public def main (args : List String) : IO UInt32 := do
  Lake.cli args
