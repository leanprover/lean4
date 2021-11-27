/-
Copyright (c) 2021 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
namespace Lake

/-- The type of a `Script`'s function. Same as that of a `main` function. -/
abbrev ScriptFn := (args : List String) → IO UInt32

/--
A package `Script` is a `ScriptFn` definition that is
indexed by a `String` key and can be be run by `lake run <key> [-- <args>]`.
-/
structure Script where
  fn : ScriptFn
  doc? : Option String
  deriving Inhabited

def Script.run (args : List String) (self : Script) : IO UInt32 :=
  self.fn args
