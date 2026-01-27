/-
Copyright (c) 2024 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
module

prelude
public import Lean.ToExpr
public import Lake.Util.Version
public import Lake.Config.Dependency
import Lean.Elab.Eval
import Lake.DSL.Syntax

open Lean Elab Term Meta

/-! # Version Literals

Defines the `v!"<ver>"` syntax for version literals.
The elaborator attempts to synthesize an instance of `DecodeVersion` for the
expected type and then applies it to the string literal.
-/

namespace Lake.DSL

public protected def SemVerCore.toExpr (self : SemVerCore) : Expr :=
  mkApp3 (mkConst ``SemVerCore.mk) (toExpr self.major) (toExpr self.minor) (toExpr self.patch)

public instance : ToExpr SemVerCore where
  toExpr := SemVerCore.toExpr
  toTypeExpr := mkConst ``SemVerCore

public protected def StdVer.toExpr (self : StdVer) : Expr :=
  mkApp2 (mkConst ``StdVer.mk) (toExpr self.toSemVerCore) (toExpr self.specialDescr)

public instance : ToExpr StdVer where
  toExpr := StdVer.toExpr
  toTypeExpr := mkConst ``StdVer

public protected def ComparatorOp.toExpr (self : ComparatorOp) : Expr :=
  match self with
  | .lt => mkConst ``ComparatorOp.lt
  | .le => mkConst ``ComparatorOp.le
  | .gt => mkConst ``ComparatorOp.gt
  | .ge => mkConst ``ComparatorOp.ge
  | .eq => mkConst ``ComparatorOp.eq
  | .ne => mkConst ``ComparatorOp.ne

public instance : ToExpr ComparatorOp where
  toExpr := ComparatorOp.toExpr
  toTypeExpr := mkConst ``ComparatorOp

public protected def VerComparator.toExpr (self : VerComparator) : Expr :=
  mkApp3 (mkConst ``VerComparator.mk) (toExpr self.ver) (toExpr self.op) (toExpr self.includeSuffixes)

public instance : ToExpr VerComparator where
  toExpr := VerComparator.toExpr
  toTypeExpr := mkConst ``VerComparator

public protected def VerRange.toExpr (self : VerRange) : Expr :=
  mkApp2 (mkConst ``VerRange.mk) (toExpr self.toString) (toExpr self.clauses)

public instance : ToExpr VerRange where
  toExpr := VerRange.toExpr
  toTypeExpr := mkConst ``VerRange

public protected def InputVer.toExpr (self : InputVer) : Expr :=
  match self with
  | .none => mkConst ``InputVer.none
  | .git rev => mkApp (mkConst ``InputVer.git) (toExpr rev)
  | .ver ver => mkApp (mkConst ``InputVer.ver) (toExpr ver)

public instance : ToExpr InputVer where
  toExpr := InputVer.toExpr
  toTypeExpr := mkConst ``InputVer

public def toResultExpr [ToExpr α] (x : Except String α) : Except String Expr :=
  Functor.map toExpr x

def evalDecodeVersion (stx : Term) (expectedType : Expr) : TermElabM Expr := do
  let ofVerT? ← mkAppM ``Except #[mkConst ``String, expectedType]
  let ofVerE ← elabTermEnsuringType (← ``(decodeVersion $stx)) ofVerT?
  let resT ← mkAppM ``Except #[mkConst ``String, mkConst ``Expr]
  let resE ← mkAppM ``toResultExpr #[ofVerE]
  match (← unsafe evalExpr (Except String Expr) resT resE) with
  | .ok ver => return ver
  | .error e => throwError e

@[builtin_term_elab evalVer]
def elabEvalVersion : TermElab := fun stx expectedType? => do
  let `(eval_ver% $v) := stx
    | throwError "ill-formed `decode_version%` syntax"
  tryPostponeIfNoneOrMVar expectedType?
  let some expectedType := expectedType?
    | throwError "expected type is not known"
  evalDecodeVersion v expectedType

@[builtin_macro verLit]
def expandVerLit : Macro := fun stx => do
  if let `(v!$v) := stx then
    `(eval_ver% s!$v)
  else
    Macro.throwError "ill-formed version literal"
