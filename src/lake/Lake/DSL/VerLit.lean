/-
Copyright (c) 2024 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
prelude
import Lean.Elab.Eval
import Lake.Util.Version

open Lean Elab Term Meta

/-! # Version Literals

Defines the `v!"<ver>"` syntax for version literals.
The elaborator attempts to synthesize an instance of `DecodeVersion` for the
expected type and then applies it to the string literal.
-/

namespace Lake

instance : ToExpr SemVerCore where
  toExpr ver := mkAppN (mkConst ``SemVerCore.mk)
    #[toExpr ver.major, toExpr ver.minor, toExpr ver.patch]
  toTypeExpr := mkConst ``SemVerCore

instance : ToExpr StdVer where
  toExpr ver := mkAppN (mkConst ``StdVer.mk)
    #[toExpr ver.toSemVerCore, toExpr ver.specialDescr]
  toTypeExpr := mkConst ``StdVer

private def toResultExpr [ToExpr α] (x : Except String α) : Except String Expr :=
  Functor.map toExpr x

/-- A Lake version literal. -/
scoped syntax:max (name := verLit) "v!" noWs interpolatedStr(term) : term

@[builtin_term_elab verLit]
def elabVerLit : TermElab := fun stx expectedType? => do
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
