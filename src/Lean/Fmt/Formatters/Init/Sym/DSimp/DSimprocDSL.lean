/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Marc Huisinga
-/
module

prelude
public import Lean.Fmt.FmtM.Basic
meta import Init.Sym.DSimp.DSimprocDSL
import Lean.Fmt.FmtM.CommonFormatters
import Init.Data

namespace Lean.Fmt

@[builtin_infix_fmt Lean.Parser.Sym.DSimp.andThen]
public def fmtSymDSimprocAndThen : Fmt.InfixOperation := {
  sparse := false
  precs? := some { prec := 60, lhsPrec := 61, rhsPrec := 60 }
}

@[builtin_infix_fmt Lean.Parser.Sym.DSimp.orElse]
public def fmtSymDSimprocOrElse : Fmt.InfixOperation := {
  sparse := false
  precs? := some { prec := 20, lhsPrec := 21, rhsPrec := 20 }
}

@[builtin_fmt Lean.Parser.Sym.DSimp.dsimprocParen]
public def fmtSymDSimprocParen : Fmt := fun
  | `(Parser.Sym.DSimp.dsimprocParen| (%$lbTk $dsimproc:sym_dsimproc )%$rbTk) => do
    let lbTk ← fmt lbTk
    let dsimproc ← fmt dsimproc
    let rbTk ← fmt rbTk
    return Layouts.parens lbTk dsimproc rbTk
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Command.symDSimpFieldPre]
public def fmtSymDSimpFieldPre : Fmt := fun
  | `(Parser.Command.symDSimpFieldPre| pre%$preTk :=%$colonEqTk $dsimproc:sym_dsimproc) => do
    let preTk ← fmt preTk
    let colonEqTk ← fmt colonEqTk
    let dsimproc ← fmt dsimproc
    return Layouts.assignmentDeclaration preTk colonEqTk dsimproc
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Command.symDSimpFieldPost]
public def fmtSymDSimpFieldPost : Fmt := fun
  | `(Parser.Command.symDSimpFieldPost| post%$postTk :=%$colonEqTk $dsimproc:sym_dsimproc) => do
    let postTk ← fmt postTk
    let colonEqTk ← fmt colonEqTk
    let dsimproc ← fmt dsimproc
    return Layouts.assignmentDeclaration postTk colonEqTk dsimproc
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Command.symDSimpFieldMaxSteps]
public def fmtSymDSimpFieldMaxSteps : Fmt := fun
  | `(Parser.Command.symDSimpFieldMaxSteps| maxSteps%$maxStepsTk :=%$colonEqTk $maxSteps:num) => do
    let maxStepsTk ← fmt maxStepsTk
    let colonEqTk ← fmt colonEqTk
    let maxSteps ← fmt maxSteps
    return Layouts.assignmentDeclaration maxStepsTk colonEqTk maxSteps
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Command.registerSymDSimp]
public def fmtRegisterSymDSimp : Fmt := fun
  | `(Parser.Command.registerSymDSimp|
      register_sym_dsimp%$registerSymDSimpTk $declId:ident where%$whereTk
        $fields:sym_dsimp_field*) => do
    let registerSymDSimpTk ← fmt registerSymDSimpTk
    let declId ← fmt declId
    let whereTk ← fmt whereTk
    let fields ← fmtArray fields
    let signature := Layouts.pseudoApplication #[registerSymDSimpTk, declId]
    let fields := Layouts.lines fields
    return Layouts.keywordSeparated signature whereTk fields { allowFlattening := false }
  | _ =>
    throw .partialFormatter
