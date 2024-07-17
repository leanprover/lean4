/-
Copyright (c) 2024 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lean.Elab.Eval

/-! # Version

This module contains useful definitions for manipulating versions.
It also defines a `v!"<ver>"` syntax for version literals.
-/

open Lean

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
structure LeanVer extends SemVerCore where
  specialDescr : String := ""
  deriving Inhabited, Repr, DecidableEq

instance : Coe LeanVer SemVerCore := ⟨LeanVer.toSemVerCore⟩

@[inline] protected def LeanVer.ofSemVerCore (ver : SemVerCore) : LeanVer :=
  {toSemVerCore := ver, specialDescr := ""}

instance : Coe SemVerCore LeanVer := ⟨LeanVer.ofSemVerCore⟩

protected def LeanVer.compare (a b : LeanVer) : Ordering :=
  match compare a.toSemVerCore b.toSemVerCore with
  | .eq =>
    match a.specialDescr, b.specialDescr with
    | "", "" => .eq
    |  _, "" => .lt
    | "",  _ => .gt
    | a, b => compare a b
  | ord => ord

instance : Ord LeanVer := ⟨LeanVer.compare⟩

instance : LT LeanVer := ltOfOrd
instance : LE LeanVer := leOfOrd
instance : Min LeanVer := minOfLe
instance : Max LeanVer := maxOfLe

def LeanVer.parse (ver : String) : Except String LeanVer := do
  let sepPos := ver.find (· == '-')
  if h : ver.atEnd sepPos then
    SemVerCore.parse ver
  else
    let core ← SemVerCore.parse <| ver.extract 0 sepPos
    let specialDescr := ver.extract (ver.next' sepPos h) ver.endPos
    if specialDescr.isEmpty then
      throw "invalid Lean version: '-' suffix cannot be empty"
    return {toSemVerCore := core, specialDescr}

protected def LeanVer.toString (ver : LeanVer) : String :=
  if ver.specialDescr.isEmpty then
    ver.toSemVerCore.toString
  else
    s!"{ver.toSemVerCore}-{ver.specialDescr}"

instance : ToString LeanVer := ⟨LeanVer.toString⟩
instance : ToJson LeanVer := ⟨(·.toString)⟩
instance : FromJson LeanVer := ⟨(do LeanVer.parse <| ← fromJson? ·)⟩

instance : ToExpr LeanVer where
  toExpr ver := mkAppN (mkConst ``LeanVer.mk)
    #[toExpr ver.toSemVerCore, toExpr ver.specialDescr]
  toTypeExpr := mkConst ``LeanVer

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
@[default_instance] instance : DecodeVersion LeanVer := ⟨LeanVer.parse⟩

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
