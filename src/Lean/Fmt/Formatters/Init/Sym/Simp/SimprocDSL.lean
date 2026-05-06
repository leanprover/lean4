/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Marc Huisinga
-/
module

prelude
public import Lean.Fmt.FmtM.Basic
meta import Init.Sym.Simp.SimprocDSL
import Lean.Fmt.FmtM.CommonFormatters
import Init.Data

namespace Lean.Fmt

@[builtin_infix_fmt Lean.Parser.Sym.Simp.andThen]
public def fmtSymSimprocAndThen : Fmt.InfixOperation := {
  sparse := false
  precs? := some { prec := 60, lhsPrec := 61, rhsPrec := 60 }
}

@[builtin_infix_fmt Lean.Parser.Sym.Simp.orElse]
public def fmtSymSimprocOrElse : Fmt.InfixOperation := {
  sparse := false
  precs? := some { prec := 20, lhsPrec := 21, rhsPrec := 20 }
}

@[builtin_fmt Lean.Parser.Sym.Simp.rewriteSet]
public def fmtSymSimpRewriteSet : Fmt := fun
  | `(Parser.Sym.Simp.rewriteSet|
      rewrite%$rewriteTk $setId:ident $[with%$withTk? $discharger?:sym_discharger]?) => do
    let rewriteTk ← fmt rewriteTk
    let setId ← fmt setId
    let withTk? ← fmt? withTk?
    let discharger? ← fmt? discharger?
    let lhs := Layouts.pseudoApplication #[rewriteTk, setId]
    let «with» := Layouts.keywordPrefixedTerm withTk? discharger?
    return Layouts.blocks #[lhs, «with»]
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Sym.Simp.rewriteInline]
public def fmtSymSimpRewriteInline : Fmt := fun
  | `(Parser.Sym.Simp.rewriteInline|
      rewrite%$rewriteTk [%$lbTk $thms:ident,* ]%$rbTk
        $[with%$withTk? $discharger?:sym_discharger]?) => do
    let rewriteTk ← fmt rewriteTk
    let lbTk ← fmt lbTk
    let thms ← fmtTSepArray thms
    let rbTk ← fmt rbTk
    let withTk? ← fmt? withTk?
    let discharger? ← fmt? discharger?
    let thms := Layouts.collection lbTk thms rbTk
    let «with» := Layouts.keywordPrefixedTerm withTk? discharger?
    return Layouts.blocks #[rewriteTk, thms, «with»]
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Sym.Simp.simprocParen]
public def fmtSymSimprocParen : Fmt := fun
  | `(Parser.Sym.Simp.simprocParen| (%$lbTk $simproc:sym_simproc )%$rbTk) => do
    let lbTk ← fmt lbTk
    let simproc ← fmt simproc
    let rbTk ← fmt rbTk
    return Layouts.parens lbTk simproc rbTk
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Sym.Simp.dischParen]
public def fmtSymDischargerParen : Fmt := fun
  | `(Parser.Sym.Simp.dischParen| (%$lbTk $discharger:sym_discharger )%$rbTk) => do
    let lbTk ← fmt lbTk
    let discharger ← fmt discharger
    let rbTk ← fmt rbTk
    return Layouts.parens lbTk discharger rbTk
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Command.symSimpFieldPre]
public def fmtSymSimpFieldPre : Fmt := fun
  | `(Parser.Command.symSimpFieldPre| pre%$preTk :=%$colonEqTk $simproc:sym_simproc) => do
    let preTk ← fmt preTk
    let colonEqTk ← fmt colonEqTk
    let simproc ← fmt simproc
    return Layouts.assignmentDeclaration preTk colonEqTk simproc
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Command.symSimpFieldPost]
public def fmtSymSimpFieldPost : Fmt := fun
  | `(Parser.Command.symSimpFieldPost| post%$postTk :=%$colonEqTk $simproc:sym_simproc) => do
    let postTk ← fmt postTk
    let colonEqTk ← fmt colonEqTk
    let simproc ← fmt simproc
    return Layouts.assignmentDeclaration postTk colonEqTk simproc
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Command.symSimpFieldMaxSteps]
public def fmtSymSimpFieldMaxSteps : Fmt := fun
  | `(Parser.Command.symSimpFieldMaxSteps| maxSteps%$maxStepsTk :=%$colonEqTk $maxSteps:num) => do
    let maxStepsTk ← fmt maxStepsTk
    let colonEqTk ← fmt colonEqTk
    let maxSteps ← fmt maxSteps
    return Layouts.assignmentDeclaration maxStepsTk colonEqTk maxSteps
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Command.symSimpFieldMaxDischargeDepth]
public def fmtSymSimpFieldMaxDischargeDepth : Fmt := fun
  | `(Parser.Command.symSimpFieldMaxDischargeDepth|
      maxDischargeDepth%$maxDischargeDepthTk :=%$colonEqTk $maxDischargeDepth:num) => do
    let maxDischargeDepthTk ← fmt maxDischargeDepthTk
    let colonEqTk ← fmt colonEqTk
    let maxDischargeDepth ← fmt maxDischargeDepth
    return Layouts.assignmentDeclaration maxDischargeDepthTk colonEqTk maxDischargeDepth
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Command.registerSymSimp]
public def fmtRegisterSymSimp : Fmt := fun
  | `(Parser.Command.registerSymSimp|
      register_sym_simp%$registerSymSimpTk $declId:ident where%$whereTk
        $fields:sym_simp_field*) => do
    let registerSymSimpTk ← fmt registerSymSimpTk
    let declId ← fmt declId
    let whereTk ← fmt whereTk
    let fields ← fmtArray fields
    let signature := Layouts.pseudoApplication #[registerSymSimpTk, declId]
    let fields := Layouts.lines fields
    return Layouts.keywordSeparated signature whereTk fields { allowFlattening := false }
  | _ =>
    throw .partialFormatter
