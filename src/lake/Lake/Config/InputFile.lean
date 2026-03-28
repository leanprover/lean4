/-
Copyright (c) 2025 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
module

prelude
public import Lake.Config.ConfigTarget

namespace Lake
open Lean System

/-- An input file -- its package plus its configuration. -/
public abbrev InputFile := ConfigTarget InputFile.configKind

/--
The full path to the input file.
That is, the package's `dir` joined with the file's `path`.
-/
@[inline] public def InputFile.path (self : InputFile) : FilePath :=
  self.pkg.dir / self.config.path

/-- Whether this is a text file. -/
@[inline] public def InputFile.text (self : InputFile) : Bool :=
  self.config.text

/-- An input directory -- its package plus its configuration. -/
public abbrev InputDir := ConfigTarget InputDir.configKind

/--
The full path to the input file.
That is, the package's `dir` joined with the file's `path`.
-/
@[inline] public def InputDir.path (self : InputDir) : FilePath :=
  self.pkg.dir / self.config.path

/-- Whether this directory contains text files. -/
@[inline] public def InputDir.text (self : InputDir) : Bool :=
  self.config.text

/-- The file inclusion filter function for the input directory. -/
@[inline] public def InputDir.filter (self : InputDir) : FilePath → Bool :=
  self.config.filter.matches
