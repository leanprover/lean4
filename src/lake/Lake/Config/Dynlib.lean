/-
Copyright (c) 2022 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
module

prelude
public import Lake.Config.OutFormat

open System Lean

namespace Lake

/-- A dynamic/shared library artifact for linking. -/
public structure Dynlib where
  /-- Library file path. -/
  path : FilePath
  /-- Library name without platform-specific prefix/suffix (for `-l`). -/
  name : String
  /-- Whether this library can be loaded as a plugin. -/
  plugin := false
  /--
  Transitive dependencies of this library for situations that need them
  (e.g., linking on Windows, loading via `lean`).
  -/
  deps : Array Dynlib := #[]
  deriving Inhabited, Repr

namespace Dynlib

/-- Optional library directory (for `-L`). -/
public def dir? (self : Dynlib) : Option FilePath :=
  self.path.parent

public instance : ToJson Dynlib := ⟨(·.path.toString)⟩
public instance : ToString Dynlib := ⟨(·.path.toString)⟩
public instance : Coe Dynlib FilePath := ⟨(·.path)⟩
