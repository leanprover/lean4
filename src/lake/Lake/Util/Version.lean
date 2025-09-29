/-
Copyright (c) 2024 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
module

prelude
public import Lean.Data.Json
public import Lake.Util.Date

/-! # Version

This module contains useful definitions for manipulating versions.
It also defines a `v!"<ver>"` syntax for version literals.
-/

open System Lean

namespace Lake

/-- The major-minor-patch triple of a [SemVer](https://semver.org/). -/
public structure SemVerCore where
  major : Nat := 0
  minor : Nat := 0
  patch : Nat := 0
  deriving Inhabited, Repr, DecidableEq, Ord

public instance : LT SemVerCore := ltOfOrd
public instance : LE SemVerCore := leOfOrd
public instance : Min SemVerCore := minOfLe
public instance : Max SemVerCore := maxOfLe

public def SemVerCore.parse (ver : String) : Except String SemVerCore := do
  try
    match ver.split (· == '.') with
    | [major, minor, patch] =>
        let parseNat (v : String) (what : String) := do
          let some v := v.toNat?
            | throw s!"expect numeral {what} version, got '{v}'"
          return v
        return {
          major := ← parseNat major "major"
          minor := ← parseNat minor "minor"
          patch := ← parseNat patch "patch"
        }
    | ps => throw s!"incorrect number of components: got {ps.length}, expected 3"
  catch e =>
    throw s!"invalid version core: {e}"

public protected def SemVerCore.toString (ver : SemVerCore) : String :=
  s!"{ver.major}.{ver.minor}.{ver.patch}"

public instance : ToString SemVerCore := ⟨SemVerCore.toString⟩
public instance : ToJson SemVerCore := ⟨(·.toString)⟩
public instance : FromJson SemVerCore := ⟨(do SemVerCore.parse <| ← fromJson? ·)⟩

/--
A Lean-style semantic version.
A major-minor-patch triple with an optional arbitrary `-` suffix.
-/
public structure StdVer extends SemVerCore where
  specialDescr : String := ""
  deriving Inhabited, Repr, DecidableEq

/-- A Lean version. -/
public abbrev LeanVer := StdVer

public instance : Coe StdVer SemVerCore := ⟨StdVer.toSemVerCore⟩

@[inline] public def StdVer.ofSemVerCore (ver : SemVerCore) : StdVer :=
  {toSemVerCore := ver, specialDescr := ""}

public instance : Coe SemVerCore StdVer := ⟨StdVer.ofSemVerCore⟩

public protected def StdVer.compare (a b : StdVer) : Ordering :=
  match compare a.toSemVerCore b.toSemVerCore with
  | .eq =>
    match a.specialDescr, b.specialDescr with
    | "", "" => .eq
    |  _, "" => .lt
    | "",  _ => .gt
    | a, b => compare a b
  | ord => ord

public instance : Ord StdVer := ⟨StdVer.compare⟩

public instance : LT StdVer := ltOfOrd
public instance : LE StdVer := leOfOrd
public instance : Min StdVer := minOfLe
public instance : Max StdVer := maxOfLe

public def StdVer.parse (ver : String) : Except String StdVer := do
  let sepPos := ver.find (· == '-')
  if h : ver.atEnd sepPos then
    SemVerCore.parse ver
  else
    let core ← SemVerCore.parse <| ver.extract 0 sepPos
    let specialDescr := ver.extract (ver.next' sepPos h) ver.endPos
    if specialDescr.isEmpty then
      throw "invalid version: '-' suffix cannot be empty"
    return {toSemVerCore := core, specialDescr}

public protected def StdVer.toString (ver : StdVer) : String :=
  if ver.specialDescr.isEmpty then
    ver.toSemVerCore.toString
  else
    s!"{ver.toSemVerCore}-{ver.specialDescr}"

public instance : ToString StdVer := ⟨StdVer.toString⟩
public instance : ToJson StdVer := ⟨(·.toString)⟩
public instance : FromJson StdVer := ⟨(do StdVer.parse <| ← fromJson? ·)⟩

/-- A Lean toolchain version. -/
public inductive ToolchainVer
| release (ver : LeanVer)
| nightly (date : Date)
| pr (no : Nat)
| other (name : String)
deriving Repr, DecidableEq

public instance : Coe LeanVer ToolchainVer := ⟨ToolchainVer.release⟩

public def ToolchainVer.defaultOrigin := "leanprover/lean4"
public def ToolchainVer.prOrigin := "leanprover/lean4-pr-releases"

public def ToolchainVer.ofString (ver : String) : ToolchainVer := Id.run do
  let colonPos := ver.posOf ':'
  let (origin, tag) :=
    if h : colonPos < ver.endPos then
      let pos := ver.next' colonPos (by simp_all [String.endPos, String.atEnd])
      (ver.extract 0 colonPos, ver.extract pos ver.endPos)
    else
      ("", ver)
  if tag.startsWith "v" then
    if let .ok ver := StdVer.parse (tag.drop 1) then
      if origin.isEmpty || origin == defaultOrigin then
        return .release ver
    return .other ver
  else if tag.startsWith "nightly-" then
    if let some date := Date.ofString? (tag.drop "nightly-".length) then
      if origin.isEmpty || origin == defaultOrigin then
        return .nightly date
  else if tag.startsWith "pr-release-" then
    if let some n := (tag.drop "pr-release-".length).toNat? then
      if origin.isEmpty || origin == prOrigin then
        return .pr n
  else
    if let .ok ver := StdVer.parse ver then
      if origin.isEmpty || origin == defaultOrigin then
        return .release ver
  return .other ver

/-- Parse a toolchain from a `lean-toolchain` file. -/
public def ToolchainVer.ofFile? (toolchainFile : FilePath) : IO (Option ToolchainVer) := do
  try
    let toolchainString ← IO.FS.readFile toolchainFile
    return some <| ToolchainVer.ofString toolchainString.trim
  catch
    | .noFileOrDirectory .. =>
      return none
    | e => throw e

/-- The `elan` toolchain file name (i.e., `lean-toolchain`). -/
public def toolchainFileName : FilePath := "lean-toolchain"

/-- Parse a toolchain from the `lean-toolchain` file of the directory `dir`. -/
@[inline] public def ToolchainVer.ofDir? (dir : FilePath) : IO (Option ToolchainVer) :=
  ToolchainVer.ofFile? (dir / toolchainFileName)

public protected def ToolchainVer.toString (ver : ToolchainVer) : String :=
  match ver with
  | .release ver => s!"{defaultOrigin}:v{ver}"
  | .nightly date => s!"{defaultOrigin}:nightly-{date}"
  | .pr n => s!"{prOrigin}:pr-release-{n}"
  | .other s => s

public instance : ToString ToolchainVer := ⟨ToolchainVer.toString⟩
public instance : ToJson ToolchainVer := ⟨(·.toString)⟩
public instance : FromJson ToolchainVer := ⟨(ToolchainVer.ofString <$> fromJson? ·)⟩

@[expose] public def ToolchainVer.lt (a b : ToolchainVer) : Prop :=
  match a, b with
  | .release v1, .release v2 => v1 < v2
  | .nightly d1, .nightly d2 => d1 < d2
  | _, _ => False

public instance : LT ToolchainVer := ⟨ToolchainVer.lt⟩

public instance ToolchainVer.decLt (a b : ToolchainVer) : Decidable (a < b) :=
  match a, b with
  | .release v1, .release v2 => inferInstanceAs (Decidable (v1 < v2))
  | .nightly d1, .nightly d2 => inferInstanceAs (Decidable (d1 < d2))
  | .release _, .pr _ | .release _, .nightly _ | .release _, .other _
  | .nightly _, .release _ | .nightly _, .pr _ | .nightly _, .other _
  | .pr _, _ | .other _, _ => .isFalse (by simp [LT.lt, ToolchainVer.lt])

@[expose] public def ToolchainVer.le (a b : ToolchainVer) : Prop :=
  match a, b with
  | .release v1, .release v2 => v1 ≤ v2
  | .nightly d1, .nightly d2 => d1 ≤ d2
  | .pr n1, .pr n2 => n1 = n2
  | .other v1, .other v2 => v1 = v2
  | _, _ => False

public instance : LE ToolchainVer := ⟨ToolchainVer.le⟩

public instance ToolchainVer.decLe (a b : ToolchainVer) : Decidable (a ≤ b) :=
  match a, b with
  | .release v1, .release v2 => inferInstanceAs (Decidable (v1 ≤ v2))
  | .nightly d1, .nightly d2 => inferInstanceAs (Decidable (d1 ≤ d2))
  | .pr n1, .pr n2 => inferInstanceAs (Decidable (n1 = n2))
  | .other v1, .other v2 => inferInstanceAs (Decidable (v1 = v2))
  | .release _, .pr _ | .release _, .nightly _ | .release _, .other _
  | .nightly _, .release _ | .nightly _, .pr _ | .nightly _, other _
  | .pr _, .release _ | .pr _, .nightly _ |  .pr _, .other _
  | .other _, .release _ | .other _, .nightly _ | .other _, .pr _ =>
    .isFalse (by simp [LE.le, ToolchainVer.le])

/-- Parses a version from a string. -/
public class DecodeVersion (α : Type u) where
  decodeVersion : String → Except String α

export DecodeVersion (decodeVersion)

public instance : DecodeVersion SemVerCore := ⟨SemVerCore.parse⟩
@[default_instance] public instance : DecodeVersion StdVer := ⟨StdVer.parse⟩
public instance : DecodeVersion ToolchainVer := ⟨(pure <| ToolchainVer.ofString ·)⟩
