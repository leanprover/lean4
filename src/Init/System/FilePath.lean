/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Sebastian Ullrich
-/
prelude
import Init.System.Platform
import Init.Control.StateRef
import Init.Data.ToString.Basic
import Init.Data.List.Control

namespace System
open Platform

structure FilePath where
  toString : String
  deriving Inhabited, DecidableEq, Hashable

instance : Repr FilePath where
  reprPrec p := Repr.addAppParen ("FilePath.mk " ++ repr p.toString)

instance : ToString FilePath where
  toString p := p.toString

namespace FilePath

/-- The character that separates directories. In the case where more than one character is possible, `pathSeparator` is the 'ideal' one. -/
def pathSeparator : Char :=
  if isWindows then '\\' else '/'

/-- The list of all possible separators. -/
def pathSeparators : List Char :=
  if isWindows then ['\\', '/'] else ['/']

/-- File extension character -/
def extSeparator : Char := '.'

def exeExtension : String :=
  if isWindows then "exe" else ""

/-- Represents a single component in a file path -/
inductive Component where
  | rootDir : Component  -- Represents the root directory (/ or C:\)
  | curDir : Component   -- Represents "."
  | parentDir : Component -- Represents ".."
  | normal : String → Component -- Represents a regular path component
  deriving Inhabited, DecidableEq

/-- Iterator state for path components -/
structure ComponentsState where
  remaining : String
  front : String.Pos := 0
  back : String.Pos
  deriving Inhabited

/-- Returns the next component and updated state -/
private def nextComponent (s : ComponentsState) : Option (Component × ComponentsState) := Id.run do
  if s.front ≥ s.back then return none

  -- Skip any leading separators
  let mut pos := s.front
  while pos < s.back && pathSeparators.contains (s.remaining.get pos) do
    pos := pos + ⟨ 1 ⟩

  if pos ≥ s.back then return none

  -- Find end of current component
  let start := pos
  while pos < s.back && !(pathSeparators.contains (s.remaining.get pos)) do
    pos := pos + ⟨ 1 ⟩

  let component := s.remaining.extract start pos

  -- Determine component type
  let comp := match component with
    | "" => Component.rootDir
    | "." => Component.curDir
    | ".." => Component.parentDir
    | c => Component.normal c

  let newState := { s with front := pos }
  some (comp, newState)



/-- Returns an iterator over the components of a path -/
def componentsList (p : FilePath) : List Component := Id.run do
  let mut comps := []
  let mut state : ComponentsState := {
    remaining := p.toString,
    back := p.toString.endPos
  }

  -- Handle root directory for absolute paths
  if isWindows && p.toString.length ≥ 2 && p.toString.get ⟨1⟩ == ':' then
    comps := Component.rootDir :: comps
    state := { state with front := ⟨ 2 ⟩ }
  else if pathSeparators.contains p.toString.front then
    comps := Component.rootDir :: comps
    state := { state with front := ⟨ 1 ⟩ }

  -- Collect remaining components
  let mut curr := nextComponent state

  while true do
    match curr with
      | none => break
      | some (comp, newState) => do
        comps := comp :: comps
        curr := nextComponent newState

  comps.reverse

/-- Converts a list of components back to a file path -/
def fromComponents (comps : List Component) : FilePath := Id.run do
  let mut parts := []
  let mut isAbs := false

  for comp in comps do
    match comp with
    | Component.rootDir =>
      if isWindows then
        parts := "C:" :: parts
      isAbs := true
    | Component.curDir => parts := "." :: parts
    | Component.parentDir => parts := ".." :: parts
    | Component.normal s => parts := s :: parts

  let joined := String.intercalate pathSeparator.toString parts.reverse
  ⟨if isAbs then pathSeparator.toString ++ joined else joined⟩

/-- Normalizes a file path by resolving . and .. components -/
def normalize (p : FilePath) : FilePath := Id.run do
  let comps := p.componentsList

  -- Process components and resolve . and ..
  let mut result := []
  let mut isAbs := false

  for comp in comps do
    match comp with
    | Component.rootDir =>
      isAbs := true
      result := [Component.rootDir]
    | Component.curDir => pure ()  -- Skip . components
    | Component.parentDir =>
      if result.isEmpty || (result.head? == some Component.parentDir && !isAbs) then
        result := Component.parentDir :: result
      else if result != [Component.rootDir] then
        result := result.tail  -- Remove last component
    | Component.normal s =>
      result := Component.normal s :: result

  fromComponents result.reverse

-- the following functions follow the names and semantics from Rust's `std::path::Path`

def isAbsolute (p : FilePath) : Bool :=
  pathSeparators.contains p.toString.front || (isWindows && p.toString.length > 1 && p.toString.iter.next.curr == ':')

def isRelative (p : FilePath) : Bool :=
  !p.isAbsolute

def join (p sub : FilePath) : FilePath :=
  if sub.isAbsolute then
    sub
  else
    ⟨p.toString ++ pathSeparator.toString ++ sub.toString⟩

instance : Div FilePath where
  div := FilePath.join

instance : HDiv FilePath String FilePath where
  hDiv p sub := FilePath.join p ⟨sub⟩

private def posOfLastSep (p : FilePath) : Option String.Pos :=
  p.toString.revFind pathSeparators.contains

def parent (p : FilePath) : Option FilePath :=
  let extractParentPath := FilePath.mk <$> p.toString.extract {} <$> posOfLastSep p
  if p.isAbsolute then
    let lengthOfRootDirectory := if pathSeparators.contains p.toString.front then 1 else 3
    if p.toString.length == lengthOfRootDirectory then
      -- `p` is a root directory
      none
    else if posOfLastSep p == String.Pos.mk (lengthOfRootDirectory - 1) then
      -- `p` is a direct child of the root
      some ⟨p.toString.extract 0 ⟨lengthOfRootDirectory⟩⟩
    else
      -- `p` is an absolute path with at least two subdirectories
      extractParentPath
  else
    -- `p` is a relative path
    extractParentPath

def fileName (p : FilePath) : Option String :=
  let lastPart := match posOfLastSep p with
    | some sepPos => p.toString.extract (sepPos + '/') p.toString.endPos
    | none        => p.toString
  if lastPart.isEmpty || lastPart == "." || lastPart == ".." then none else some lastPart

/-- Extracts the stem (non-extension) part of `p.fileName`. -/
def fileStem (p : FilePath) : Option String :=
  p.fileName.map fun fname =>
    match fname.revPosOf '.' with
    | some ⟨0⟩ => fname
    | some pos => fname.extract 0 pos
    | none     => fname

def extension (p : FilePath) : Option String :=
  p.fileName.bind fun fname =>
    match fname.revPosOf '.' with
    | some 0   => none
    | some pos => fname.extract (pos + '.') fname.endPos
    | none     => none

def withFileName (p : FilePath) (fname : String) : FilePath :=
  match p.parent with
  | none => ⟨fname⟩
  | some p => p / fname

/-- Appends the extension `ext` to a path `p`.

`ext` should not contain a leading `.`, as this function adds one.
If `ext` is the empty string, no `.` is added.

Unlike `System.FilePath.withExtension`, this does not remove any existing extension. -/
def addExtension (p : FilePath) (ext : String) : FilePath :=
  match p.fileName with
  | none => p
  | some fname => p.withFileName (if ext.isEmpty then fname else fname ++ "." ++ ext)

/-- Replace the current extension in a path `p` with `ext`.

`ext` should not contain a `.`, as this function adds one.
If `ext` is the empty string, no `.` is added. -/
def withExtension (p : FilePath) (ext : String) : FilePath :=
  match p.fileStem with
  | none => p
  | some stem => p.withFileName (if ext.isEmpty then stem else stem ++ "." ++ ext)

def components (p : FilePath) : List String :=
  p.normalize |>.toString.splitOn pathSeparator.toString

end FilePath

def mkFilePath (parts : List String) : FilePath :=
  ⟨String.intercalate FilePath.pathSeparator.toString parts⟩

instance : Coe String FilePath where
  coe := FilePath.mk

abbrev SearchPath := List FilePath

namespace SearchPath

/-- The character that is used to separate the entries in the $PATH (or %PATH%) environment variable. -/
protected def separator : Char :=
  if isWindows then ';' else ':'

def parse (s : String) : SearchPath :=
  s.split (fun c => SearchPath.separator == c) |>.map FilePath.mk

def toString (path : SearchPath) : String :=
  SearchPath.separator.toString.intercalate (path.map FilePath.toString)

end SearchPath

end System
