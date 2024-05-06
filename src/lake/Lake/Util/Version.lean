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
  major : Nat
  minor : Nat
  patch : Nat
  deriving DecidableEq, Ord

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
instance : ToJson SemVerCore := ⟨fun v => SemVerCore.toString v⟩
instance : FromJson SemVerCore := ⟨fun v => do SemVerCore.parse (← fromJson? v)⟩

instance : ToExpr SemVerCore where
  toExpr ver := mkAppN (mkConst ``SemVerCore.mk)
    #[toExpr ver.major, toExpr ver.minor, toExpr ver.patch]
  toTypeExpr := mkConst ``SemVerCore

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

private def toResultExpr [ToExpr α] (x : Except String α) : Except String Expr :=
  Functor.map toExpr x

/-- A Lake version literal. -/
scoped syntax:max (name := verLit) "v!" noWs str : term

@[term_elab verLit] def elabVerLit : TermElab := fun stx expectedType? => do
  let `(v!$v) := stx | throwUnsupportedSyntax
  tryPostponeIfNoneOrMVar expectedType?
  let some expectedType := expectedType?
    | throwError "expected type is not known"
  let ofVerT? ← mkAppM ``Except #[mkConst ``String, expectedType]
  let ofVerE ← elabTermEnsuringType (← ``(decodeVersion $v)) ofVerT?
  let resT ← mkAppM ``Except #[mkConst ``String, mkConst ``Expr]
  let resE ← mkAppM ``toResultExpr #[ofVerE]
  match (← unsafe evalExpr (Except String Expr) resT resE) with
  | .ok ver => return ver
  | .error e => throwError e
