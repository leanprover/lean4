/-
Copyright (c) 2024 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
prelude
import Lean.Data.Json

open System Lean

namespace Lake

/--
Convert a relative file path to a platform-independent string.
Uses `/` as the path separator, even on Windows.
-/
def mkRelPathString (path : FilePath) : String :=
  if System.Platform.isWindows then
    path.toString.map fun c => if c = '\\' then '/' else c
  else
    path.toString

scoped instance : ToJson FilePath where
  toJson path := toJson <| mkRelPathString path

/--
Joins a two (potentially) relative paths.
If either path is `.`, this returns the other.
-/
def joinRelative (a b : FilePath) : System.FilePath :=
  if b == "." then a
  else if a == "." then b
  else inline FilePath.join a b

scoped instance : Div FilePath where
  div := joinRelative

scoped instance : HDiv FilePath String FilePath where
  hDiv p sub := joinRelative p ⟨sub⟩
