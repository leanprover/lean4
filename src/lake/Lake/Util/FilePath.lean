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

/--
Creates a module `Name` from a file path.
The components of the path become string components of the `Name`.
Before conversion, normalizes the path, removes any extensions, and
strips a trailing path separator.

Examples:
* ``modOfFilePath "Foo/Bar" = `Foo.Bar``
* ``modOfFilePath "Foo/Bar/" = `Foo.Bar``
* ``modOfFilePath "Foo/Bar.lean" = `Foo.Bar``
* ``modOfFilePath "Foo/Bar.tar.gz" = `Foo.Bar``
* ``modOfFilePath "Foo/Bar.lean/" = `Foo.«Bar.lean»``
-/
def modOfFilePath (path : FilePath) : Name :=
  let path := removeExts path.normalize.toString
  let path := path.stripSuffix FilePath.pathSeparator.toString
  FilePath.components path |>.foldl .str .anonymous
where
  removeExts (s : String) (i := s.endPos) (e := s.endPos) :=
    if h : i = 0 then
      s.extract 0 e
    else
      have := String.prev_lt_of_pos s i h
      let i' := s.prev i
      let c  := s.get i'
      if c == FilePath.pathSeparator then
        s.extract 0 e
      else if c == '.' then
        removeExts s i' i'
      else
        removeExts s i' e
  termination_by i.1

-- sanity check
example :
  modOfFilePath "Foo/Bar" = `Foo.Bar
  ∧ modOfFilePath "Foo/Bar/" = `Foo.Bar
  ∧ modOfFilePath "Foo/Bar.lean" = `Foo.Bar
  ∧ modOfFilePath "Foo/Bar.tar.gz" = `Foo.Bar
  ∧ modOfFilePath "Foo/Bar.lean/" = `Foo.«Bar.lean»
:= by native_decide
