/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Marc Huisinga
-/
module

prelude
public import Lean.Fmt.FmtM.Basic
public import Lean.Fmt.Formatters.Init.Tactics
meta import Init.Conv
import Lean.Fmt.FmtM.CommonFormatters
import Init.Data

namespace Lean.Fmt

open Lean.Parser.Tactic.Conv

@[builtin_fmt Lean.Parser.Tactic.Conv.convSeq1Indented]
public def fmtConvSeq1Indented : Fmt := fun
  | `(Parser.Tactic.Conv.convSeq1Indented| $convs:conv;*) => do fmtSeq convs none
  | _ => throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.Conv.convSeqBracketed]
public def fmtConvSeqBracketed : Fmt := fun
  | `(Parser.Tactic.Conv.convSeqBracketed|
      {%$lbTk
        $convs:conv;*
      }%$rbTk ) => do
    let lbTk ← fmt lbTk
    let convs ← fmtSeq convs none
    let rbTk ← fmt rbTk
    return Layouts.bracketed lbTk convs rbTk <| .sparse hardNl
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.Conv.convSeq]
public def fmtConvSeq : Fmt := fun
  | `(Parser.Tactic.Conv.convSeq| $s:convSeqBracketed) => fmt s
  | `(Parser.Tactic.Conv.convSeq| $s:convSeq1Indented) => fmt s
  | _ => throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.Conv.occsIndexed]
public def fmtConvOccsIndexed : Fmt := fun
  | `(Parser.Tactic.Conv.occsIndexed| $nums:num*) => do
    let nums ← fmtArray nums
    return Layouts.fill nums
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.Conv.occs]
public def fmtConvOccs : Fmt := fun
  | `(Parser.Tactic.Conv.occs| (%$lbTk occs%$occsTk :=%$colonEqTk $body )%$rbTk) =>
    fmtNamedArgumentTerm lbTk occsTk colonEqTk body rbTk
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.Conv.argArg]
public def fmtConvArgArg : Fmt := fun
  | `(Parser.Tactic.Conv.argArg| $[@%$atTk?]? $[-%$negTk?]? $n:num) => do
    let atTk? ← fmt? atTk?
    let negTk? ← fmt? negTk?
    let n ← fmt n
    return Layouts.atomic #[atTk?, negTk?, n]
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.Conv.withAnnotateState]
public def fmtConvWithAnnotateState : Fmt := fun stx => do
  let withAnnotateStateTk ← getStxArg! stx 0
  let rawStx ← getStxArg! stx 1
  let conv ← getStxArg! stx 2
  let withAnnotateStateTk ← fmt withAnnotateStateTk
  let rawStx ← fmt rawStx
  let conv ← fmt conv
  return Layouts.pseudoApplication #[withAnnotateStateTk, rawStx, conv]

@[builtin_fmt Lean.Parser.Tactic.Conv.arg]
public def fmtConvArgTactic : Fmt := fun
  | `(conv| arg%$argTk $a:argArg) => do
    let argTk ← fmt argTk
    let a ← fmt a
    return Layouts.pseudoApplication #[argTk, a]
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.Conv.ext]
public def fmtConvExt : Fmt := fun
  | `(conv| ext%$extTk $args:binderIdent*) => do
    let extTk ← fmt extTk
    let args ← fmtArray args
    return Layouts.pseudoApplication <| #[extTk] ++ args
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.Conv.change]
public def fmtConvChange : Fmt := fun
  | `(conv| change%$changeTk $t:term) => do
    let changeTk ← fmt changeTk
    let t ← fmt t
    return Layouts.pseudoApplication #[changeTk, t]
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.Conv.delta]
public def fmtConvDelta : Fmt := fun
  | `(conv| delta%$deltaTk $ids:ident*) => do
    let deltaTk ← fmt deltaTk
    let ids ← fmtArray ids
    return Layouts.pseudoApplication <| #[deltaTk] ++ ids
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.Conv.unfold]
public def fmtConvUnfold : Fmt := fun
  | `(conv| unfold%$unfoldTk $ids:ident*) => do
    let unfoldTk ← fmt unfoldTk
    let ids ← fmtArray ids
    return Layouts.pseudoApplication <| #[unfoldTk] ++ ids
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.Conv.clear]
public def fmtConvClear : Fmt := fun stx => do
  let `(conv| clear $args:term*) := stx
    | throw .partialFormatter
  let clearTk ← fmt (← getStxArg! stx 0)
  let args ← fmtArray args
  return Layouts.pseudoApplication (format := { parenthesize := true }) <| #[clearTk] ++ args

@[builtin_fmt Lean.Parser.Tactic.Conv.convIntro___]
public def fmtConvIntro : Fmt := fun
  | `(conv| intro%$introTk $args:binderIdent*) => do
    let introTk ← fmt introTk
    let args ← fmtArray args
    return Layouts.pseudoApplication <| #[introTk] ++ args
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.Conv.convApply_]
public def fmtConvApply : Fmt := fun
  | `(conv| apply%$applyTk $e:term) => do
    let applyTk ← fmt applyTk
    let e ← fmt e
    return Layouts.pseudoApplication #[applyTk, e]
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.Conv.nestedTacticCore]
public def fmtConvNestedTacticCore : Fmt := fun
  | `(conv| tactic'%$tk =>%$arrowTk $seq:tacticSeq) => do
    let tk ← fmt tk
    let arrowTk ← fmt arrowTk
    let seq ← fmt seq
    return Layouts.assignmentDeclaration tk arrowTk seq
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.Conv.nestedTactic]
public def fmtConvNestedTactic : Fmt := fun
  | `(conv| tactic%$tk =>%$arrowTk $seq:tacticSeq) => do
    let tk ← fmt tk
    let arrowTk ← fmt arrowTk
    let seq ← fmt seq
    return Layouts.assignmentDeclaration tk arrowTk seq
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.Conv.convTactic]
public def fmtConvTacticInTactic : Fmt := fun
  | `(tactic| conv'%$tk =>%$arrowTk $s:convSeq) => do
    let tk ← fmt tk
    let arrowTk ← fmt arrowTk
    let s ← fmt s
    return Layouts.assignmentDeclaration tk arrowTk s
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.Conv.convConvSeq]
public def fmtConvConvSeq : Fmt := fun
  | `(conv| conv%$tk =>%$arrowTk $s:convSeq) => do
    let tk ← fmt tk
    let arrowTk ← fmt arrowTk
    let s ← fmt s
    return Layouts.assignmentDeclaration tk arrowTk s
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.Conv.nestedConv]
public def fmtConvNestedConv : Fmt := fun
  | `(Parser.Tactic.Conv.nestedConv| $s:convSeqBracketed) => fmt s
  | _ => throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.Conv.paren]
public def fmtConvParen : Fmt := fun
  | `(conv| (%$lbTk $s:convSeq )%$rbTk) => do
    let lbTk ← fmt lbTk
    let s ← fmt s
    let rbTk ← fmt rbTk
    return Layouts.parenthesizedSeq lbTk s rbTk
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.Conv.allGoals]
public def fmtConvAllGoals : Fmt := fun
  | `(conv| all_goals%$tk $s:convSeq) => do
    let tk ← fmt tk
    let s ← fmt s
    return Layouts.keywordPrefixedSeq tk s .nonSticky
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.Conv.anyGoals]
public def fmtConvAnyGoals : Fmt := fun
  | `(conv| any_goals%$tk $s:convSeq) => do
    let tk ← fmt tk
    let s ← fmt s
    return Layouts.keywordPrefixedSeq tk s .nonSticky
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.Conv.focus]
public def fmtConvFocus : Fmt := fun
  | `(conv| focus%$tk $s:convSeq) => do
    let tk ← fmt tk
    let s ← fmt s
    return Layouts.keywordPrefixedSeq tk s .nonSticky
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.Conv.failIfSuccess]
public def fmtConvFailIfSuccess : Fmt := fun
  | `(conv| fail_if_success%$tk $s:convSeq) => do
    let tk ← fmt tk
    let s ← fmt s
    return Layouts.keywordPrefixedSeq tk s .nonSticky
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.Conv.convTry_]
public def fmtConvTry : Fmt := fun
  | `(conv| try%$tk $s:convSeq) => do
    let tk ← fmt tk
    let s ← fmt s
    return Layouts.keywordPrefixedSeq tk s .nonSticky
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.Conv.convRepeat_]
public def fmtConvRepeat : Fmt := fun
  | `(conv| repeat%$tk $s:convSeq) => do
    let tk ← fmt tk
    let s ← fmt s
    return Layouts.keywordPrefixedSeq tk s .nonSticky
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.Conv.case]
public def fmtConvCase : Fmt := fun
  | `(conv| case%$caseTk $args:caseArg|* =>%$arrowTk $s:convSeq) =>
    fmtCaseDeclaration caseTk args arrowTk s
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.Conv.case']
public def fmtConvCase' : Fmt := fun
  | `(conv| case'%$caseTk $args:caseArg|* =>%$arrowTk $s:convSeq) =>
    fmtCaseDeclaration caseTk args arrowTk s
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.Conv.«convNext__=>_»]
public def fmtConvNext : Fmt := fun
  | `(conv| next%$nextTk $args:binderIdent* =>%$arrowTk $s:convSeq) =>
    fmtNextLike nextTk args arrowTk s
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.Conv.«conv·_»]
public def fmtConvDot : Fmt := fun
  | `(conv| ·%$dotTk $s:convSeq) => do
    let dotTk ← fmt dotTk
    let s ← fmt s
    return nested <| Layouts.softSpacedAtomic #[dotTk, s]
  | _ =>
    throw .partialFormatter

@[builtin_infix_fmt Lean.Parser.Tactic.Conv.«conv_<;>_»]
public def fmtConvSeqFocus : Fmt.InfixOperation := {
  sparse := false
  precs? := some { prec := 1, lhsPrec := 0, rhsPrec := 0 }
}

@[builtin_fmt Lean.Parser.Tactic.Conv.convRw__]
public def fmtConvRw : Fmt := fun
  | `(conv| rw%$rwTk $cfg:optConfig $rules:rwRuleSeq) => fmtRwLike rwTk cfg rules none
  | _ => throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.Conv.convErw__]
public def fmtConvErw : Fmt := fun
  | `(conv| erw%$erwTk $cfg:optConfig $rules:rwRuleSeq) => fmtRwLike erwTk cfg rules none
  | _ => throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.Conv.rewrite]
public def fmtConvRewrite : Fmt := fun
  | `(conv| rewrite%$rewriteTk $cfg:optConfig $rules:rwRuleSeq) =>
    fmtRwLike rewriteTk cfg rules none
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.Conv.simp]
public def fmtConvSimp : Fmt := fun
  | `(conv| simp%$simpTk $cfg:optConfig $[$disch:discharger]? $[only%$only?]?
      $[[%$lbTk? $args?,* ]%$rbTk?]?) =>
    fmtSimpLike #[simpTk] cfg disch only? lbTk? args? rbTk? none
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.Conv.dsimp]
public def fmtConvDSimp : Fmt := fun
  | `(conv| dsimp%$dsimpTk $cfg:optConfig $[$disch:discharger]? $[only%$only?]?
      $[[%$lbTk? $args?,* ]%$rbTk?]?) =>
    fmtSimpLike #[dsimpTk] cfg disch only? lbTk? args? rbTk? none
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.Conv.simpTrace]
public def fmtConvSimpTrace : Fmt := fun
  | `(conv| simp?%$tk $cfg:optConfig $[$disch:discharger]? $[only%$only?]?
      $[[%$lbTk? $args?,* ]%$rbTk?]?) =>
    fmtSimpLike #[tk] cfg disch only? lbTk? args? rbTk? none
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.Conv.dsimpTrace]
public def fmtConvDSimpTrace : Fmt := fun
  | `(conv| dsimp?%$tk $cfg:optConfig $[only%$only?]? $[[%$lbTk? $args?,* ]%$rbTk?]?) =>
    fmtSimpLike #[tk] cfg none only? lbTk? args? rbTk? none
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.Conv.pattern]
public def fmtConvPattern : Fmt := fun
  | `(conv| pattern%$patternTk $[$occs?:occs]? $t:term) => do
    let patternTk ← fmt patternTk
    let occs? ← fmt? occs?
    let «pattern» := Layouts.pseudoApplication #[patternTk, occs?]
    let t ← fmt t
    return Layouts.pseudoApplication #[«pattern», t]
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.Conv.extractLets]
public def fmtConvExtractLets : Fmt := fun
  | `(conv| extract_lets%$tk $cfg:optConfig $args*) => fmtExtractLetsLike tk cfg args none
  | _ => throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.Conv.liftLets]
public def fmtConvLiftLets : Fmt := fun
  | `(conv| lift_lets%$tk $cfg:optConfig) => fmtLiftLetsLike tk cfg
  | _ => throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.Conv.enterPattern]
public def fmtConvEnterPattern : Fmt := fun
  | `(Parser.Tactic.Conv.enterPattern| in%$inTk $[$occs?:occs]? $t:term) => do
    let inTk ← fmt inTk
    let occs? ← fmt? occs?
    let «in» := Layouts.pseudoApplication #[inTk, occs?]
    let t ← fmt t
    return Layouts.pseudoApplication #[«in», t]
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.Conv.enterArg]
public def fmtConvEnterArg : Fmt := fun
  | `(Parser.Tactic.Conv.enterArg| $x:binderIdent) => fmt x
  | `(Parser.Tactic.Conv.enterArg| $x:argArg) => fmt x
  | `(Parser.Tactic.Conv.enterArg| $x:enterPattern) => fmt x
  | _ => throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.Conv.enter]
public def fmtConvEnter : Fmt := fun
  | `(conv| enter%$enterTk [%$lbTk $args:enterArg,* ]%$rbTk) => do
    let enterTk ← fmt enterTk
    let lbTk ← fmt lbTk
    let args ← fmtTSepArray args
    let rbTk ← fmt rbTk
    let args := Layouts.collection lbTk args rbTk
    return Layouts.pseudoApplication #[enterTk, args]
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.Conv.first]
public def fmtConvFirst : Fmt := fun
  | `(conv| first%$firstTk $[|%$barTks $convs:convSeq]*) => fmtAltsTactic firstTk barTks convs
  | _ => throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.Conv.conv]
public def fmtConvTactic : Fmt := fun
  | `(tactic| conv%$convTk $[at%$atTk? $id?:ident]? $[in%$inTk? $[$occs?:occs]? $t?:term]?
      =>%$arrowTk $s:convSeq) => do
    let convTk ← fmt convTk
    let atTk? ← fmt? atTk?
    let id? ← fmt? id?
    let inTk? ← fmt? inTk?
    let occs? ← fmt? occs?.join
    let inLhs := Layouts.pseudoApplication #[inTk?, occs?]
    let t? ← fmt? t?
    let arrowTk ← fmt arrowTk
    let s ← fmt s
    let «at» := Layouts.keywordPrefixedTerm atTk? id?
    let «in» := Layouts.keywordPrefixedTerm inLhs t?
    let lhs := Layouts.blocks #[convTk, «at», «in»]
    return Layouts.assignmentDeclaration lhs arrowTk s
  | _ =>
    throw .partialFormatter
