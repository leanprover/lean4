/-
Copyright (c) 2021 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
module

prelude
public import Init.Dynamic
public import Init.System.IO
public import Lake.Util.Exit
public import Lake.Config.Context

namespace Lake

/--
The type of a `Script`'s monad.

It is an `IO` monad equipped information about the Lake configuration.
-/
public abbrev ScriptM := LakeT IO

/--
The type of a `Script`'s function.

It is similar to the `main` function's signature, except the monad is
also equipped with information about the Lake configuration.
-/
public abbrev ScriptFn := (args : List String) → ScriptM ExitCode

public instance : TypeName ScriptFn := unsafe (.mk _ ``ScriptFn)

/--
A package `Script` is a named `ScriptFn` definition with a some optional documentation.

It can be run by `lake run <name> [-- <args>]`.
-/
public structure Script where
  /-- The full name of the `Script` (e.g., `pkg/script`). -/
  name : String
  fn : ScriptFn
  doc? : Option String
  deriving Inhabited

/-- Run the `script` with the specified CLI `args`. -/
public def Script.run (args : List String) (self : Script) : ScriptM ExitCode :=
  self.fn args
