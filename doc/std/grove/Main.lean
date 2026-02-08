/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import GroveStdlib.Std
import GroveStdlib.Generated

def config : Grove.Framework.Project.Configuration where
  projectNamespace := `GroveStdlib

def project : Grove.Framework.Project where
  config := config
  rootNode := GroveStdlib.std
  restoreState := GroveStdlib.Generated.restoreState

def main (args : List String) : IO UInt32 :=
  Grove.Framework.main project #[`Init, `Std, `Lean] args
