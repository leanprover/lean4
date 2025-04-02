/-
Copyright (c) 2025 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
prelude
import Lake.Config.Meta
import Lake.Config.Pattern

open Lean System

namespace Lake

/-- The declarative configuration for a single input file. -/
configuration InputFileConfig (name : Name) where
  /--
  The path to the input file (relative to the package root).

  Defaults to the name of the target.
  -/
  path : FilePath := name.toString (escape := false)
  /--
  Whether this is a text file.
  If so, Lake normalize line endings for its trace.
  This avoids rebuilds across platforms with different line endings.

  Defaults to `false`.
  -/
  text : Bool := false

instance : EmptyCollection (InputFileConfig name) := ⟨{}⟩

/-- The declarative configuration for an input directory. -/
configuration InputDirConfig (name : Name) where
  /--
  The path to the input directory (relative to the package root).

  Defaults to the name of the target.
  -/
  path : FilePath := name.toString (escape := false)
  /--
  Whether the directory is composed of text files.
  If so, Lake normalize line endings for their traces.
  This avoids rebuilds across platforms with different line endings.

  Defaults to `false`.
  -/
  text : Bool := false
  /-
  Includes only the files from the directory
  whose paths statisify the pattern.

  Defaults to including every file.
  -/
  filter : PathPat := .star

instance : EmptyCollection (InputDirConfig name) := ⟨{}⟩
