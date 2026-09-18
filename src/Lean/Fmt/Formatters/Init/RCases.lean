/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Marc Huisinga
-/
module

prelude
public import Lean.Fmt.FmtM.Basic
meta import Init.RCases
import Lean.Fmt.FmtM.CommonFormatters
import Init.Data

namespace Lean.Fmt

@[builtin_fmt Lean.Parser.Tactic.rcasesPatMed]
public def fmtRCasesPatMed : Fmt := fun
  | `(Parser.Tactic.rcasesPatMed| $pats:rcasesPat|*) => do
    let pats ← fmtTSepArray pats
    return nested <| Layouts.horizontalOrVertical <| joinAltPats empty pats
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.rcasesPatLo]
public def fmtRCasesPatLo : Fmt := fun
  | `(Parser.Tactic.rcasesPatLo| $pat:rcasesPatMed $[:%$colonTk? $type?:term]?) => do
    let pat ← fmt pat
    let colonTk? ← fmt? colonTk?
    let type? ← fmt? type?
    return Layouts.typeAscription pat colonTk? type?
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.rcasesPat.one]
public def fmtRCasesPatOne : Fmt := fun
  | `(rcasesPat| $x:ident) => fmt x
  | _ => throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.rcasesPat.explicit]
public def fmtRCasesPatExplicit : Fmt := fun
  | `(rcasesPat| @%$atTk$pat:rcasesPat) => do
    let atTk ← fmt atTk
    let pat ← fmt pat
    return Layouts.prefixOperator atTk pat .withoutSpacing
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.rcasesPat.tuple]
public def fmtRCasesPatTuple : Fmt := fun
  | `(rcasesPat| ⟨%$lbTk $pats:rcasesPatLo,* ⟩%$rbTk) => do
    let lbTk ← fmt lbTk
    let pats ← fmtTSepArray pats
    let rbTk ← fmt rbTk
    return Layouts.tuple lbTk pats rbTk
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.rcasesPat.paren]
public def fmtRCasesPatParen : Fmt := fun
  | `(rcasesPat| (%$lbTk $pat:rcasesPatLo )%$rbTk) => do
    let lbTk ← fmt lbTk
    let pat ← fmt pat
    let rbTk ← fmt rbTk
    return Layouts.parens lbTk pat rbTk
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.rintroPat.one]
public def fmtRIntroPatOne : Fmt := fun
  | `(rintroPat| $pat:rcasesPat) => fmt pat
  | _ => throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.rintroPat.binder]
public def fmtRIntroPatBinder : Fmt := fun
  | `(rintroPat| (%$lbTk $pats:rintroPat* $[:%$typeAscriptionTk? $type?:term]? )%$rbTk) =>
    fmtBinder #[lbTk] pats #[] typeAscriptionTk? type? none #[rbTk]
      (kind := .local (respectPseudoAlignment := true))
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.rcases]
public def fmtTacticRCases : Fmt := fun
  | `(tactic| rcases%$rcasesTk $targets:elimTarget,* $[with%$withTk? $pat?:rcasesPatLo]?) => do
    let rcasesTk ← fmt rcasesTk
    let targets ← fmtTSepArray targets
    let withTk? ← fmt? withTk?
    let pat? ← fmt? pat?
    let lhs := Layouts.keywordPrefixedSepFill rcasesTk targets .nonSticky
    let «with» := Layouts.keywordPrefixedTerm withTk? pat?
    return Layouts.pseudoApplication #[lhs, «with»]
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.obtain]
public def fmtTacticObtain : Fmt := fun
  | `(tactic| obtain%$obtainTk $[$pat?:rcasesPatMed]? $[:%$colonTk? $type?:term]? $[:=%$assignTk? $vals?,*]?) =>
    do
      let obtainTk ← fmt obtainTk
      let pat? ← fmt? pat?
      let colonTk? ← fmt? colonTk?
      let type? ← fmt? type?
      let assignTk? ← fmt? assignTk?
      let annotatedPat := Layouts.typeAscription pat? colonTk? type?
      let signature := Layouts.pseudoApplication #[obtainTk, annotatedPat]
      let vals ← fmtTSepArray <| vals?.getD ⟨#[]⟩
      let vals := Layouts.sepHorizontalOrVertical vals (includeSeps := true)
      return Layouts.assignmentDeclaration signature assignTk? vals
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.rintro]
public def fmtTacticRIntro : Fmt := fun
  | `(tactic| rintro%$rintroTk $pats:rintroPat* $[:%$colonTk? $type?:term]?) => do
    let rintroTk ← fmt rintroTk
    let pats ← fmtArray pats
    let colonTk? ← fmt? colonTk?
    let type? ← fmt? type?
    let pats := Layouts.fill pats
    let annotatedPats := Layouts.typeAscription pats colonTk? type?
    return Layouts.pseudoApplication #[rintroTk, annotatedPats]
  | _ =>
    throw .partialFormatter
