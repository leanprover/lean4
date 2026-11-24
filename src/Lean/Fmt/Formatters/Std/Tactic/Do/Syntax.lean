/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Marc Huisinga
-/
module

prelude
public import Lean.Fmt.FmtM.Basic
meta import Std.Tactic.Do.Syntax
import Lean.Fmt.FmtM.CommonFormatters
import Lean.Fmt.Formatters.Std.WP.Tactic
import Init.Data

namespace Lean.Fmt

@[builtin_fmt Lean.Parser.Tactic.mclear]
public def fmtMClear : Fmt := fun
  | `(tactic| mclear%$mclearTk $h:ident) => do
    let mclearTk ← fmt mclearTk
    let h ← fmt h
    return Layouts.pseudoApplication #[mclearTk, h]
  | _ => throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.mexact]
public def fmtMExact : Fmt := fun
  | `(tactic| mexact%$mexactTk $e:term) => do
    let mexactTk ← fmt mexactTk
    let e ← fmt e
    return Layouts.pseudoApplication #[mexactTk, e]
  | _ => throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.mpure]
public def fmtMPure : Fmt := fun
  | `(tactic| mpure%$mpureTk $h:ident) => do
    let mpureTk ← fmt mpureTk
    let h ← fmt h
    return Layouts.pseudoApplication #[mpureTk, h]
  | _ => throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.mrenameI]
public def fmtMRenameI : Fmt := fun
  | `(tactic| mrename_i%$mrenameITk $hs:binderIdent*) => do
    let mrenameITk ← fmt mrenameITk
    let hs ← fmtArray hs
    return Layouts.pseudoApplication <| #[mrenameITk] ++ hs
  | _ => throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.mspecialize]
public def fmtMSpecialize : Fmt := fun
  | `(tactic| mspecialize%$mspecializeTk $h:ident $args:term*) => do
    let mspecializeTk ← fmt mspecializeTk
    let h ← fmt h
    let args ← fmtArray args
    return Layouts.pseudoApplication <| #[mspecializeTk, h] ++ args
  | _ => throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.mspecializePure]
public def fmtMSpecializePure : Fmt := fun
  | `(tactic| mspecialize_pure%$mspecializePureTk $h:term $args:term* =>%$arrowTk $name:ident) => do
    let mspecializePureTk ← fmt mspecializePureTk
    let h ← fmt h
    let args ← fmtArray args
    let arrowTk ← fmt arrowTk
    let name ← fmt name
    let lhs := Layouts.pseudoApplication <| #[h] ++ args
    let assignment := Layouts.assignmentDeclaration lhs arrowTk name
    return Layouts.pseudoApplication #[mspecializePureTk, assignment]
  | _ => throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.mrefine]
public def fmtMRefine : Fmt := fun
  | `(tactic| mrefine%$mrefineTk $pat:mrefinePat) => do
    let mrefineTk ← fmt mrefineTk
    let pat ← fmt pat
    return Layouts.pseudoApplication #[mrefineTk, pat]
  | _ => throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.mintro]
public def fmtMIntro : Fmt := fun
  | `(tactic| mintro%$mintroTk $pats:mintroPat*) => do
    let mintroTk ← fmt mintroTk
    let pats ← fmtArray pats
    return Layouts.pseudoApplication <| #[mintroTk] ++ pats
  | _ => throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.mrevert]
public def fmtMRevert : Fmt := fun
  | `(tactic| mrevert%$mrevertTk $pats:mrevertPat*) => do
    let mrevertTk ← fmt mrevertTk
    let pats ← fmtArray pats
    return Layouts.pseudoApplication <| #[mrevertTk] ++ pats
  | _ => throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.mspecNoBind]
public def fmtMSpecNoBind : Fmt := fun
  | `(tactic| mspec_no_bind%$mspecNoBindTk $[$spec?:term]?) => do
    let mspecNoBindTk ← fmt mspecNoBindTk
    let spec? ← fmt? spec?
    return Layouts.pseudoApplication #[mspecNoBindTk, spec?]
  | _ => throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.mspecNoSimp]
public def fmtMSpecNoSimp : Fmt := fun
  | `(tactic| mspec_no_simp%$mspecNoSimpTk $[$spec?:term]?) => do
    let mspecNoSimpTk ← fmt mspecNoSimpTk
    let spec? ← fmt? spec?
    return Layouts.pseudoApplication #[mspecNoSimpTk, spec?]
  | _ => throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.mspec]
public def fmtMSpec : Fmt := fun
  | `(tactic| mspec%$mspecTk $[$spec?:term]?) => do
    let mspecTk ← fmt mspecTk
    let spec? ← fmt? spec?
    return Layouts.pseudoApplication #[mspecTk, spec?]
  | _ => throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.mexists]
public def fmtMExists : Fmt := fun
  | `(tactic| mexists%$mexistsTk $witnesses:term,*) => do
    let mexistsTk ← fmt mexistsTk
    let witnesses ← fmtTSepArray witnesses
    return Layouts.pseudoApplication #[mexistsTk, Layouts.sepFill witnesses]
  | _ => throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.mdup]
public def fmtMDup : Fmt := fun
  | `(tactic| mdup%$mdupTk $h:ident =>%$arrowTk $h':ident) => do
    let mdupTk ← fmt mdupTk
    let h ← fmt h
    let arrowTk ← fmt arrowTk
    let h' ← fmt h'
    let assignment := Layouts.assignmentDeclaration h arrowTk h'
    return Layouts.pseudoApplication #[mdupTk, assignment]
  | _ => throw .partialFormatter

public def fmtMHaveLike
    (keywordTk h : Syntax) (typeAscriptionTk? type? : Option Syntax) (colonEqTk body : Syntax)
    : FmtM TaggedDoc := do
  let keywordTk ← fmt keywordTk
  let h ← fmt h
  let typeAscriptionTk? ← fmt? typeAscriptionTk?
  let type? ← fmt? type?
  let colonEqTk ← fmt colonEqTk
  let body ← fmt body
  let decl := Layouts.typeAscription h typeAscriptionTk? type?
  let signature := Layouts.letDecl keywordTk empty decl
  return Layouts.assignmentDeclaration signature colonEqTk body

@[builtin_fmt Lean.Parser.Tactic.mhave]
public def fmtMHave : Fmt := fun
  | `(tactic| mhave%$mhaveTk $h:ident $[:%$typeAscriptionTk? $type?:term]? :=%$colonEqTk $body:term) =>
    fmtMHaveLike mhaveTk h typeAscriptionTk? type? colonEqTk body
  | _ => throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.mreplace]
public def fmtMReplace : Fmt := fun
  | `(tactic| mreplace%$mreplaceTk $h:ident $[:%$typeAscriptionTk? $type?:term]? :=%$colonEqTk $body:term) =>
    fmtMHaveLike mreplaceTk h typeAscriptionTk? type? colonEqTk body
  | _ => throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.mcasesPatAlts]
public def fmtMCasesPatAlts : Fmt := fun
  | `(Parser.Tactic.mcasesPatAlts| $pats:mcasesPat|*) => do
    let pats ← fmtTSepArray pats
    return nested <| Layouts.horizontalOrVertical <| joinAltPats empty pats
  | _ => throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.mcasesPat_]
public def fmtMCasesPatOne : Fmt := fun
  | `(mcasesPat| $h:binderIdent) => fmt h
  | _ => throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.«mcasesPat-»]
public def fmtMCasesPatClear : Fmt := fmtAtomic

@[builtin_fmt Lean.Parser.Tactic.«mcasesPat⟨_⟩»]
public def fmtMCasesPatTuple : Fmt := fun
  | `(mcasesPat| ⟨%$lbTk $pats:mcasesPatAlts,* ⟩%$rbTk) => do
    let lbTk ← fmt lbTk
    let pats ← fmtTSepArray pats
    let rbTk ← fmt rbTk
    return Layouts.tuple lbTk pats rbTk
  | _ => throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.«mcasesPat(_)»]
public def fmtMCasesPatParen : Fmt := fun
  | `(mcasesPat| (%$lbTk $pat:mcasesPatAlts )%$rbTk) => do
    let lbTk ← fmt lbTk
    let pat ← fmt pat
    let rbTk ← fmt rbTk
    return Layouts.parens lbTk pat rbTk
  | _ => throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.«mcasesPat⌜_⌝»]
public def fmtMCasesPatPure : Fmt := fun
  | `(mcasesPat| ⌜%$lbTk $h:binderIdent ⌝%$rbTk) => do
    let lbTk ← fmt lbTk
    let h ← fmt h
    let rbTk ← fmt rbTk
    return Layouts.parens lbTk h rbTk
  | _ => throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.«mcasesPat□_»]
public def fmtMCasesPatStateful : Fmt := fun
  | `(mcasesPat| □%$boxTk $h:binderIdent) => do
    let boxTk ← fmt boxTk
    let h ← fmt h
    return Layouts.prefixOperator boxTk h .withoutSpacingIfAtomic
  | _ => throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.«mcasesPat%_»]
public def fmtMCasesPatPureAbbrev : Fmt := fun
  | `(mcasesPat| %%$percentTk $h:binderIdent) => do
    let percentTk ← fmt percentTk
    let h ← fmt h
    return Layouts.prefixOperator percentTk h .withoutSpacingIfAtomic
  | _ => throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.«mcasesPat#_»]
public def fmtMCasesPatStatefulAbbrev : Fmt := fun
  | `(mcasesPat| #%$hashTk $h:binderIdent) => do
    let hashTk ← fmt hashTk
    let h ← fmt h
    return Layouts.prefixOperator hashTk h .withoutSpacingIfAtomic
  | _ => throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.mcases]
public def fmtMCases : Fmt := fun
  | `(tactic| mcases%$mcasesTk $h:ident with%$withTk $pat:mcasesPat) => do
    let mcasesTk ← fmt mcasesTk
    let h ← fmt h
    let withTk ← fmt withTk
    let pat ← fmt pat
    let lhs := Layouts.pseudoApplication #[mcasesTk, h]
    let «with» := Layouts.keywordPrefixedTerm withTk pat
    return Layouts.pseudoApplication #[lhs, «with»]
  | _ => throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.mrefinePat_]
public def fmtMRefinePatOne : Fmt := fun
  | `(mrefinePat| $h:binderIdent) => fmt h
  | _ => throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.«mrefinePat⟨_⟩»]
public def fmtMRefinePatTuple : Fmt := fun
  | `(mrefinePat| ⟨%$lbTk $pats:mrefinePat,* ⟩%$rbTk) => do
    let lbTk ← fmt lbTk
    let pats ← fmtTSepArray pats
    let rbTk ← fmt rbTk
    return Layouts.tuple lbTk pats rbTk
  | _ => throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.«mrefinePat(_)»]
public def fmtMRefinePatParen : Fmt := fun
  | `(mrefinePat| (%$lbTk $pat:mrefinePat )%$rbTk) => do
    let lbTk ← fmt lbTk
    let pat ← fmt pat
    let rbTk ← fmt rbTk
    return Layouts.parens lbTk pat rbTk
  | _ => throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.«mrefinePat⌜_⌝»]
public def fmtMRefinePatPure : Fmt := fun
  | `(mrefinePat| ⌜%$lbTk $e:term ⌝%$rbTk) => do
    let lbTk ← fmt lbTk
    let e ← fmt e
    let rbTk ← fmt rbTk
    return Layouts.parens lbTk e rbTk
  | _ => throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.«mrefinePat□_»]
public def fmtMRefinePatStateful : Fmt := fun
  | `(mrefinePat| □%$boxTk $h:binderIdent) => do
    let boxTk ← fmt boxTk
    let h ← fmt h
    return Layouts.prefixOperator boxTk h .withoutSpacingIfAtomic
  | _ => throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.mrefinePat?_]
public def fmtMRefinePatHole : Fmt := fun
  | `(mrefinePat| ?%$questionTk $h:binderIdent) => do
    let questionTk ← fmt questionTk
    let h ← fmt h
    return Layouts.prefixOperator questionTk h .withoutSpacingIfAtomic
  | _ => throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.«mrefinePat%_»]
public def fmtMRefinePatPureAbbrev : Fmt := fun
  | `(mrefinePat| %%$percentTk $e:term) => do
    let percentTk ← fmt percentTk
    let e ← fmt e
    return Layouts.prefixOperator percentTk e .withoutSpacingIfAtomic
  | _ => throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.«mrefinePat#_»]
public def fmtMRefinePatStatefulAbbrev : Fmt := fun
  | `(mrefinePat| #%$hashTk $h:binderIdent) => do
    let hashTk ← fmt hashTk
    let h ← fmt h
    return Layouts.prefixOperator hashTk h .withoutSpacingIfAtomic
  | _ => throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.mintroPat_]
public def fmtMIntroPatCases : Fmt := fun
  | `(mintroPat| $pat:mcasesPat) => fmt pat
  | _ => throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.«mintroPat∀_»]
public def fmtMIntroPatForall : Fmt := fun
  | `(mintroPat| ∀%$forallTk $h:binderIdent) => do
    let forallTk ← fmt forallTk
    let h ← fmt h
    return Layouts.prefixOperator forallTk h .withSpacing
  | _ => throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.mrevertPat_]
public def fmtMRevertPatOne : Fmt := fun
  | `(mrevertPat| $h:ident) => fmt h
  | _ => throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.«mrevertPat∀_»]
public def fmtMRevertPatForall : Fmt := fun
  | `(mrevertPat| ∀%$forallTk $[$n?:num]?) => do
    let forallTk ← fmt forallTk
    let n? ← fmt? n?
    return Layouts.prefixOperator forallTk n? .withSpacing
  | _ => throw .partialFormatter

public def fmtVCAlt : Syntax → FmtM Layouts.Types.Alt := fun
  | `(Parser.Tactic.vcAlt| |%$pipeTk $args:caseArg|* =>%$arrowTk $seq:tacticSeq) => do
    let pipeTk ← fmt pipeTk
    let args ← fmtTSepArray args
    let arrowTk ← fmt arrowTk
    let seq ← fmt seq
    let subAlts := joinAltPats pipeTk args
    return Layouts.alt subAlts arrowTk seq
  | _ => throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.vcAlts]
public def fmtVCAlts : Fmt := fun
  | `(Parser.Tactic.vcAlts| with%$withTk $[$tac?:tactic]? $[$alts:vcAlt]*) => do
    let withTk ← fmt withTk
    let tac? ← fmt? tac?
    let alts ← alts.mapM fmtVCAlt
    let keyword := Layouts.pseudoApplication #[withTk, tac?]
    return Layouts.keywordPrefixedAlts keyword alts
  | _ => throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.mvcgen]
public def fmtMVCGen : Fmt := fun
  | `(tactic| mvcgen%$mvcgenTk $cfg:optConfig $[[%$lbTk? $args?,* ]%$rbTk?]?
      $[$invariantAlts?:invariantAlts]? $[$vcAlts?:vcAlts]?) => do
    let head ← fmtVCGenHead mvcgenTk cfg
    let args ← fmtVCGenSimpArgs lbTk? args? rbTk?
    let invariantAlts? ← fmt? invariantAlts?
    let vcAlts? ← fmt? vcAlts?
    let invariantsBlock := { block := invariantAlts?, hardNestedIfFirst := false }
    let vcAltsBlock := { block := vcAlts?, hardNestedIfFirst := false }
    return Layouts.blocks #[head, args, invariantsBlock, vcAltsBlock]
  | _ => throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.mvcgenHint]
public def fmtMVCGenHint : Fmt := fun
  | `(tactic| mvcgen?%$mvcgenTk $cfg:optConfig $[[%$lbTk? $args?,* ]%$rbTk?]?) => do
    let head ← fmtVCGenHead mvcgenTk cfg
    let args ← fmtVCGenSimpArgs lbTk? args? rbTk?
    return Layouts.pseudoApplication #[head, args]
  | _ => throw .partialFormatter
