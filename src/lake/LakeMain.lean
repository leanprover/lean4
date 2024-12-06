/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner, Sebastian Ullrich, Mac Malone
-/
prelude
import Lake
import Lake.CLI

def main (args : List String) : IO UInt32 := do
  Lake.cli args -- should not throw errors (outside user code)
