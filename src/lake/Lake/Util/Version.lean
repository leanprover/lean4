/-
Copyright (c) 2024 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lean.Elab.Eval
import Lake.Util.Date

/-! # Version

This module contains useful definitions for manipulating versions.
It also defines a `v!"<ver>"` syntax for version literals.
-/

open System Lean

namespace Lake

/-- The major-minor-patch triple of a [SemVer](https://semver.org/). -/
structure SemVerCore where
  major : Nat := 0
  minor : Nat := 0
  patch : Nat := 0
  deriving Inhabited, Repr, DecidableEq, Ord

instance : LT SemVerCore := ltOfOrd
instance : LE SemVerCore := leOfOrd
instance : Min SemVerCore := minOfLe
instance : Max SemVerCore := maxOfLe

def SemVerCore.parse (ver : String) : Except String SemVerCore := do
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

protected def SemVerCore.toString (ver : SemVerCore) : String :=
  s!"{ver.major}.{ver.minor}.{ver.patch}"

instance : ToString SemVerCore := ⟨SemVerCore.toString⟩
instance : ToJson SemVerCore := ⟨(·.toString)⟩
instance : FromJson SemVerCore := ⟨(do SemVerCore.parse <| ← fromJson? ·)⟩

instance : ToExpr SemVerCore where
  toExpr ver := mkAppN (mkConst ``SemVerCore.mk)
    #[toExpr ver.major, toExpr ver.minor, toExpr ver.patch]
  toTypeExpr := mkConst ``SemVerCore

/--
A Lean-style semantic version.
A major-minor-patch triple with an optional arbitrary `-` suffix.
-/
structure StdVer extends SemVerCore where
  specialDescr : String := ""
  deriving Inhabited, Repr, DecidableEq

/-- A Lean version. -/
abbrev LeanVer := StdVer

instance : Coe StdVer SemVerCore := ⟨StdVer.toSemVerCore⟩

@[inline] protected def StdVer.ofSemVerCore (ver : SemVerCore) : StdVer :=
  {toSemVerCore := ver, specialDescr := ""}

instance : Coe SemVerCore StdVer := ⟨StdVer.ofSemVerCore⟩

protected def StdVer.compare (a b : StdVer) : Ordering :=
  match compare a.toSemVerCore b.toSemVerCore with
  | .eq =>
    match a.specialDescr, b.specialDescr with
    | "", "" => .eq
    |  _, "" => .lt
    | "",  _ => .gt
    | a, b => compare a b
  | ord => ord

instance : Ord StdVer := ⟨StdVer.compare⟩

instance : LT StdVer := ltOfOrd
instance : LE StdVer := leOfOrd
instance : Min StdVer := minOfLe
instance : Max StdVer := maxOfLe

def StdVer.parse (ver : String) : Except String StdVer := do
  let sepPos := ver.find (· == '-')
  if h : ver.atEnd sepPos then
    SemVerCore.parse ver
  else
    let core ← SemVerCore.parse <| ver.extract 0 sepPos
    let specialDescr := ver.extract (ver.next' sepPos h) ver.endPos
    if specialDescr.isEmpty then
      throw "invalid Lean version: '-' suffix cannot be empty"
    return {toSemVerCore := core, specialDescr}

protected def StdVer.toString (ver : StdVer) : String :=
  if ver.specialDescr.isEmpty then
    ver.toSemVerCore.toString
  else
    s!"{ver.toSemVerCore}-{ver.specialDescr}"

instance : ToString StdVer := ⟨StdVer.toString⟩
instance : ToJson StdVer := ⟨(·.toString)⟩
instance : FromJson StdVer := ⟨(do StdVer.parse <| ← fromJson? ·)⟩

instance : ToExpr StdVer where
  toExpr ver := mkAppN (mkConst ``StdVer.mk)
    #[toExpr ver.toSemVerCore, toExpr ver.specialDescr]
  toTypeExpr := mkConst ``StdVer

/-- A Lean toolchain version. -/
inductive ToolchainVer
| release (ver : LeanVer)
| nightly (date : Date)
| pr (no : Nat)
| other (name : String)
deriving Repr, DecidableEq

instance : Coe LeanVer ToolchainVer := ⟨ToolchainVer.release⟩

def ToolchainVer.defaultOrigin := "leanprover/lean4"
def ToolchainVer.prOrigin := "leanprover/lean4-pr-releases"

def ToolchainVer.ofString (ver : String) : ToolchainVer := Id.run do
  let colonPos := ver.posOf ':'
  let (origin, tag) :=
    if h : colonPos < ver.endPos then
      let pos := ver.next' colonPos (by simp_all [h, String.endPos, String.atEnd])
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
def ToolchainVer.ofFile? (toolchainFile : FilePath) : IO (Option ToolchainVer) := do
  try
    let toolchainString ← IO.FS.readFile toolchainFile
    return some <| ToolchainVer.ofString toolchainString.trim
  catch
    | .noFileOrDirectory .. =>
      return none
    | e => throw e

/-- The `elan` toolchain file name (i.e., `lean-toolchain`). -/
def toolchainFileName : FilePath := "lean-toolchain"

/-- Parse a toolchain from the `lean-toolchain` file of the directory `dir`. -/
@[inline] def ToolchainVer.ofDir? (dir : FilePath) : IO (Option ToolchainVer) :=
  ToolchainVer.ofFile? (dir / toolchainFileName)

protected def ToolchainVer.toString (ver : ToolchainVer) : String :=
  match ver with
  | .release ver => s!"{defaultOrigin}:v{ver}"
  | .nightly date => s!"{defaultOrigin}:nightly-{date}"
  | .pr n => s!"{prOrigin}:pr-release-{n}"
  | .other s => s

instance : ToString ToolchainVer := ⟨ToolchainVer.toString⟩
instance : ToJson ToolchainVer := ⟨(·.toString)⟩
instance : FromJson ToolchainVer := ⟨(ToolchainVer.ofString <$> fromJson? ·)⟩

protected def ToolchainVer.lt (a b : ToolchainVer) : Prop :=
  match a, b with
  | .release v1, .release v2 => v1 < v2
  | .nightly d1, .nightly d2 => d1 < d2
  | _, _ => False

instance : LT ToolchainVer := ⟨ToolchainVer.lt⟩

instance ToolchainVer.decLt (a b : ToolchainVer) : Decidable (a < b) :=
  match a, b with
  | .release v1, .release v2 => inferInstanceAs (Decidable (v1 < v2))
  | .nightly d1, .nightly d2 => inferInstanceAs (Decidable (d1 < d2))
  | .release _, .pr _ | .release _, .nightly _ | .release _, .other _
  | .nightly _, .release _ | .nightly _, .pr _ | .nightly _, .other _
  | .pr _, _ | .other _, _ => .isFalse (by simp [LT.lt, ToolchainVer.lt])

protected def ToolchainVer.le (a b : ToolchainVer) : Prop :=
  match a, b with
  | .release v1, .release v2 => v1 ≤ v2
  | .nightly d1, .nightly d2 => d1 ≤ d2
  | .pr n1, .pr n2 => n1 = n2
  | .other v1, .other v2 => v1 = v2
  | _, _ => False

instance : LE ToolchainVer := ⟨ToolchainVer.le⟩

instance ToolchainVer.decLe (a b : ToolchainVer) : Decidable (a ≤ b) :=
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

/-! ## Version Literals

Defines the `v!"<ver>"` syntax for version literals.
The elaborator attempts to synthesize an instance of `ToVersion` for the
expected type and then applies it to the string literal.
-/

open Elab Term Meta

/-- Parses a version from a string. -/
class DecodeVersion (α : Type u) where
  decodeVersion : String → Except String α

export DecodeVersion (decodeVersion)

instance : DecodeVersion SemVerCore := ⟨SemVerCore.parse⟩
@[default_instance] instance : DecodeVersion StdVer := ⟨StdVer.parse⟩
instance : DecodeVersion ToolchainVer := ⟨(pure <| ToolchainVer.ofString ·)⟩

private def toResultExpr [ToExpr α] (x : Except String α) : Except String Expr :=
  Functor.map toExpr x

/-- A Lake version literal. -/
scoped syntax:max (name := verLit) "v!" noWs interpolatedStr(term) : term

@[term_elab verLit] def elabVerLit : TermElab := fun stx expectedType? => do
  let `(v!$v) := stx | throwUnsupportedSyntax
  tryPostponeIfNoneOrMVar expectedType?
  let some expectedType := expectedType?
    | throwError "expected type is not known"
  let ofVerT? ← mkAppM ``Except #[mkConst ``String, expectedType]
  let ofVerE ← elabTermEnsuringType (← ``(decodeVersion s!$v)) ofVerT?
  let resT ← mkAppM ``Except #[mkConst ``String, mkConst ``Expr]
  let resE ← mkAppM ``toResultExpr #[ofVerE]
  match (← unsafe evalExpr (Except String Expr) resT resE) with
  | .ok ver => return ver
  | .error e => throwError e
