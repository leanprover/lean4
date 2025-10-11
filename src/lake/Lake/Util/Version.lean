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

/-- The `elan` toolchain file name (i.e., `lean-toolchain`). -/
public def toolchainFileName : FilePath := "lean-toolchain"

public def ToolchainVer.defaultOrigin := "leanprover/lean4"
public def ToolchainVer.prOrigin := "leanprover/lean4-pr-releases"

public section -- for `@[computed_field]`
open ToolchainVer in
/-- A Lean toolchain version. -/
inductive ToolchainVer
| release (ver : LeanVer)
| nightly (date : Date)
| pr (n : Nat)
| other (v : String)
with
  @[computed_field] toString : ToolchainVer → String
    | .release ver => s!"{defaultOrigin}:v{ver}"
    | .nightly date => s!"{defaultOrigin}:nightly-{date}"
    | .pr n => s!"{prOrigin}:pr-release-{n}"
    | .other v => v
deriving Repr, DecidableEq
end

namespace ToolchainVer

public instance : Coe LeanVer ToolchainVer := ⟨ToolchainVer.release⟩

public def ofString (ver : String) : ToolchainVer := Id.run do
  let colonPos := ver.posOf ':'
  let (origin, tag) :=
    if h : colonPos < ver.endPos then
      let pos := ver.next' colonPos (by simp_all [String.endPos, String.atEnd])
      (ver.extract 0 colonPos, ver.extract pos ver.endPos)
    else
      ("", ver)
  let noOrigin := origin.isEmpty
  if tag.startsWith "v" then
    if let .ok ver := StdVer.parse (tag.drop 1) then
      if noOrigin|| origin == defaultOrigin then
        return .release ver
  else if let some date := tag.dropPrefix? "nightly-" then
    if let some date := Date.ofString? date.toString then
      if noOrigin then
        return .nightly date
      else if let some suffix := origin.dropPrefix? defaultOrigin then
        if suffix.isEmpty || suffix == "-nightly".toSubstring then
          return .nightly date
  else if let some n := tag.dropPrefix?  "pr-release-" then
    if let some n := n.toNat? then
      if noOrigin || origin == prOrigin then
        return .pr n
  else if let .ok ver := StdVer.parse ver then
    if noOrigin || origin == defaultOrigin then
      return .release ver
  return .other ver

/-- Parse a toolchain from a `lean-toolchain` file. -/
public def ofFile? (toolchainFile : FilePath) : IO (Option ToolchainVer) := do
  try
    let toolchainString ← IO.FS.readFile toolchainFile
    return some <| ToolchainVer.ofString toolchainString.trim
  catch
    | .noFileOrDirectory .. =>
      return none
    | e => throw e

/-- Parse a toolchain from the `lean-toolchain` file of the directory `dir`. -/
@[inline] public def ofDir? (dir : FilePath) : IO (Option ToolchainVer) :=
  ToolchainVer.ofFile? (dir / toolchainFileName)

public instance : ToString ToolchainVer := ⟨ToolchainVer.toString⟩
public instance : ToJson ToolchainVer := ⟨(·.toString)⟩
public instance : FromJson ToolchainVer := ⟨(ToolchainVer.ofString <$> fromJson? ·)⟩

public def blt (a b : ToolchainVer) : Bool :=
  match a, b with
  | .release v1, .release v2 => v1 < v2
  | .nightly d1, .nightly d2 => d1 < d2
  | _, _ => false

public instance : LT ToolchainVer := ⟨(·.blt ·)⟩
public instance decLt (a b : ToolchainVer) : Decidable (a < b) :=
  decidable_of_bool (a.blt b) Iff.rfl

public def ble (a b : ToolchainVer) : Bool :=
  match a, b with
  | .release v1, .release v2 => v1 ≤ v2
  | .nightly d1, .nightly d2 => d1 ≤ d2
  | .pr n1, .pr n2 => n1 = n2
  | .other v1, .other v2 => v1 = v2
  | _, _ => false

public instance : LE ToolchainVer := ⟨(·.ble ·)⟩
public instance decLe (a b : ToolchainVer) : Decidable (a ≤ b) :=
  decidable_of_bool (a.ble b) Iff.rfl

end ToolchainVer

/-- Converts a toolchain version to its normal form (e.g., with an origin). -/
public def normalizeToolchain (s : String) : String :=
  ToolchainVer.ofString s |>.toString

/-- Parses a version from a string. -/
public class DecodeVersion (α : Type u) where
  decodeVersion : String → Except String α

export DecodeVersion (decodeVersion)

public instance : DecodeVersion SemVerCore := ⟨SemVerCore.parse⟩
@[default_instance] public instance : DecodeVersion StdVer := ⟨StdVer.parse⟩
public instance : DecodeVersion ToolchainVer := ⟨(pure <| ToolchainVer.ofString ·)⟩
