/-
Copyright (c) 2022 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
prelude
import Lake.Config.OutFormat

open System Lean

namespace Lake

/-- A dynamic/shared library for linking. -/
structure Dynlib where
  /-- Library file path. -/
  path : FilePath
  /-- Library name without platform-specific prefix/suffix (for `-l`). -/
  name : String

/-- Optional library directory (for `-L`). -/
def Dynlib.dir? (self : Dynlib) : Option FilePath :=
  self.path.parent

instance : ToText Dynlib := ⟨(·.path.toString)⟩
instance : ToJson Dynlib := ⟨(·.path.toString)⟩
