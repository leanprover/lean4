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
