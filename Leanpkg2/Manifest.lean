/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner, Sebastian Ullrich, Mac Malone
-/
import Leanpkg2.LeanVersion

open System

namespace Leanpkg2

inductive Source where
  | path (dir : FilePath) : Source
  | git (url rev : String) (branch : Option String) : Source

structure Dependency where
  name : String
  src : Source

structure Manifest where
  name : String
  version : String
  leanVersion : String := leanVersionString
  timeout : Option Nat := none
  path : Option FilePath := none
  dependencies : List Dependency := []

namespace Manifest

def effectivePath (m : Manifest) : FilePath :=
  m.path.getD ⟨"."⟩

end Manifest
