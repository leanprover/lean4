/-
Copyright (c) 2021 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
prelude
import Lake.Util.Exit
import Lake.Config.Context

namespace Lake

/--
The type of a `Script`'s monad.
`IO` equipped information about the Lake configuration.
-/
abbrev ScriptM := LakeT IO

/--
The type of a `Script`'s function.
Similar to the `main` function's signature, except that its monad is
also equipped with information about the Lake configuration.
-/
abbrev ScriptFn := (args : List String) → ScriptM ExitCode

/--
A package `Script` is a `ScriptFn` definition that is
indexed by a `String` key and can be run by `lake run <key> [-- <args>]`.
-/
structure Script where
  /-- The full name of the `Script` (e.g., `pkg/script`). -/
  name : String
  fn : ScriptFn
  doc? : Option String
  deriving Inhabited

def Script.run (args : List String) (self : Script) : ScriptM ExitCode :=
  self.fn args
