/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.System.Platform
import Init.Data.String.Basic

namespace System
-- TODO: make opaque?
abbrev FilePath := String

namespace FilePath
open Platform

/-- The character that separates directories. In the case where more than one character is possible, `pathSeparator` is the 'ideal' one. -/
def pathSeparator : Char :=
  if isWindows then '\\' else '/'

/-- The list of all possible separators. -/
def pathSeparators : List Char :=
  if isWindows then ['\\', '/'] else ['/']

/-- The character that is used to separate the entries in the $PATH (or %PATH%) environment variable. -/
def searchPathSeparator : Char :=
  if isWindows then ';' else ':'

def splitSearchPath (s : String) : List String :=
  s.split (fun c => searchPathSeparator == c)

/-- File extension character -/
def extSeparator : Char := '.'

def exeSuffix : String :=
if isWindows then ".exe" else ""

/-- Case-insensitive file system -/
def isCaseInsensitive : Bool := isWindows || isOSX

-- TODO: normalize `a/`, `a//b`, etc.
def normalize (p : FilePath) (normalizeCase := isCaseInsensitive) : FilePath :=
  if pathSeparators.length == 1 && !normalizeCase then p
  else p.map fun c =>
    if pathSeparators.contains c then pathSeparator
    else if normalizeCase then c.toLower
    else c

-- the following functions follow the names and semantics from Rust's `std::path::Path`

def isAbsolute (p : FilePath) : Bool :=
  pathSeparators.contains p.front || (isWindows && p.bsize >= 1 && p[1] == ':')

def isRelative (p : FilePath) : Bool :=
  !p.isAbsolute

def join (p sub : FilePath) : FilePath :=
  if sub.isAbsolute then
    sub
  else
    p ++ pathSeparator.toString ++ sub

instance : Div FilePath where
  div := FilePath.join

-- when `FilePath` is opaque
--instance : HDiv FilePath String FilePath where
--  hDiv := FilePath.join

private def posOfLastSep (p : FilePath) : Option String.Pos :=
  p.revFind pathSeparators.contains

def parent (p : FilePath) : Option FilePath :=
  p.extract 0 <$> posOfLastSep p

def fileName (p : FilePath) : Option String :=
  let lastPart := match posOfLastSep p with
    | some sepPos => p.extract (sepPos + 1) p.bsize
    | none        => p
  if lastPart.isEmpty || lastPart == "." || lastPart == ".." then none else some lastPart

/-- Extracts the stem (non-extension) part of `p.fileName`. -/
def fileStem (p : FilePath) : Option String :=
  p.fileName.map fun fname =>
    match fname.revPosOf '.' with
    | some 0   => fname
    | some pos => fname.extract 0 pos
    | none     => fname

def extension (p : FilePath) : Option String :=
  p.fileName.bind fun fname =>
    match fname.revPosOf '.' with
    | some 0   => none
    | some pos => fname.extract (pos + 1) fname.bsize
    | none     => none

def withFileName (p : FilePath) (fname : String) : FilePath :=
  match p.parent with
  | none => fname
  | some p => p / fname

def withExtension (p : FilePath) (ext : String) : FilePath :=
  match p.fileStem with
  | none => p
  | some stem => p.withFileName (if ext.isEmpty then stem else stem ++ "." ++ ext)

def components (p : FilePath) : List String :=
  p.normalize (normalizeCase := false) |>.splitOn pathSeparator.toString

end FilePath

def mkFilePath (parts : List String) : FilePath :=
  String.intercalate FilePath.pathSeparator.toString parts

end System
