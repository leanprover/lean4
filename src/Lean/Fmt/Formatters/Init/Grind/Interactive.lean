/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Marc Huisinga
-/
module

prelude
public import Lean.Fmt.FmtM.Basic
public import Lean.Fmt.Formatters.Init.Tactics
meta import Init.Grind.Interactive
meta import Init.Grind.Attr
import Lean.Fmt.FmtM.CommonFormatters
import Init.Data

namespace Lean.Fmt

@[builtin_fmt Lean.Parser.Tactic.anchor]
public def fmtGrindAnchor : Fmt := fun
  | `(Parser.Tactic.anchor| #%$hashTk$n:hexnum) => do
    let hashTk ← fmt hashTk
    -- `hexnum` is formatted by `fmtHexnum` (`Formatters/Lean/Parser/Extra.lean`). Until its
    -- `@[builtin_fmt hexnum]` attribute is bootstrapped into stage0, `fmt` falls back to `fmtRaw`
    -- (identical output) and the linter reports `hexnum` as missing.
    let n ← fmt n
    return Layouts.atomic #[hashTk, n]
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.grindLemma]
public def fmtGrindLemma : Fmt := fun
  | `(Parser.Tactic.grindLemma| $[$mod?:grindMod]? $t:term) => do
    let mod? ← fmt? mod?
    let t ← fmt t
    return Layouts.pseudoApplication #[mod?, t]
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.grindLemmaMin]
public def fmtGrindLemmaMin : Fmt := fun
  | `(Parser.Tactic.grindLemmaMin| !%$bangTk $[$mod?:grindMod]? $t:term) => do
    let bangTk ← fmt bangTk
    let mod? ← fmt? mod?
    let t ← fmt t
    let termWithMod := Layouts.pseudoApplication #[mod?, t]
    return Layouts.prefixOperator bangTk termWithMod .withoutSpacingIfAtomic
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.grindErase]
public def fmtGrindErase : Fmt := fun
  | `(Parser.Tactic.grindErase| -%$minusTk $id:ident) => do
    let minusTk ← fmt minusTk
    let id ← fmt id
    return Layouts.atomic #[minusTk, id]
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.grindParam]
public def fmtGrindParam : Fmt := fun stx => do fmt (← getStxArg! stx 0)

@[builtin_fmt Lean.Parser.Tactic.Grind.thmNs]
public def fmtGrindThmNs : Fmt := fun
  | `(Parser.Tactic.Grind.thmNs| namespace%$nsTk $id:ident) => do
    let nsTk ← fmt nsTk
    let id ← fmt id
    return Layouts.pseudoApplication #[nsTk, id]
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.Grind.thm]
public def fmtGrindThm : Fmt := fun stx => do fmt (← getStxArg! stx 0)

@[builtin_fmt Lean.Parser.Tactic.Grind.grind_filter_]
public def fmtGrindFilterIdent : Fmt := fun
  | `(grind_filter| $id:ident) => fmt id
  | _ => throw .partialFormatter

public def fmtGrindFilterGenCmp (genTk opTk : Syntax) (n : TSyntax `num) : FmtM TaggedDoc := do
  let genTk ← fmt genTk
  let opTk ← fmt opTk
  let n ← fmt n
  return Layouts.infixOperator (format := .dense) #[genTk, opTk, n]

@[builtin_fmt Lean.Parser.Tactic.Grind.«grind_filterGen<_»]
public def fmtGrindFilterGenLt : Fmt := fun
  | `(grind_filter| gen%$genTk <%$opTk $n:num) => fmtGrindFilterGenCmp genTk opTk n
  | _ => throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.Grind.«grind_filterGen=_»]
public def fmtGrindFilterGenEq : Fmt := fun
  | `(grind_filter| gen%$genTk =%$opTk $n:num) => fmtGrindFilterGenCmp genTk opTk n
  | _ => throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.Grind.«grind_filterGen!=_»]
public def fmtGrindFilterGenNe : Fmt := fun
  | `(grind_filter| gen%$genTk !=%$opTk $n:num) => fmtGrindFilterGenCmp genTk opTk n
  | _ => throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.Grind.«grind_filterGen≤_»]
public def fmtGrindFilterGenLe : Fmt := fun
  | `(grind_filter| gen%$genTk ≤%$opTk $n:num) => fmtGrindFilterGenCmp genTk opTk n
  | _ => throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.Grind.«grind_filterGen<=_»]
public def fmtGrindFilterGenLeAscii : Fmt := fun
  | `(grind_filter| gen%$genTk <=%$opTk $n:num) => fmtGrindFilterGenCmp genTk opTk n
  | _ => throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.Grind.«grind_filterGen>_»]
public def fmtGrindFilterGenGt : Fmt := fun
  | `(grind_filter| gen%$genTk >%$opTk $n:num) => fmtGrindFilterGenCmp genTk opTk n
  | _ => throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.Grind.«grind_filterGen≥_»]
public def fmtGrindFilterGenGe : Fmt := fun
  | `(grind_filter| gen%$genTk ≥%$opTk $n:num) => fmtGrindFilterGenCmp genTk opTk n
  | _ => throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.Grind.«grind_filterGen>=_»]
public def fmtGrindFilterGenGeAscii : Fmt := fun
  | `(grind_filter| gen%$genTk >=%$opTk $n:num) => fmtGrindFilterGenCmp genTk opTk n
  | _ => throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.Grind.«grind_filter(_)»]
public def fmtGrindFilterParen : Fmt := fun
  | `(grind_filter| (%$lbTk $f:grind_filter )%$rbTk) => do
    let lbTk ← fmt lbTk
    let f ← fmt f
    let rbTk ← fmt rbTk
    return Layouts.parens lbTk f rbTk
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.Grind.«grind_filter_&&_»]
public def fmtGrindFilterAnd : Fmt := fun
  | `(grind_filter| $a:grind_filter &&%$opTk $b:grind_filter) => do
    let a ← fmt a
    let opTk ← fmt opTk
    let b ← fmt b
    return Layouts.infixOperator (format := .dense) #[a, opTk, b]
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.Grind.«grind_filter_||_»]
public def fmtGrindFilterOr : Fmt := fun
  | `(grind_filter| $a:grind_filter ||%$opTk $b:grind_filter) => do
    let a ← fmt a
    let opTk ← fmt opTk
    let b ← fmt b
    return Layouts.infixOperator (format := .dense) #[a, opTk, b]
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.Grind.grind_filter!_]
public def fmtGrindFilterNot : Fmt := fun
  | `(grind_filter| !%$bangTk $f:grind_filter) => do
    let bangTk ← fmt bangTk
    let f ← fmt f
    return Layouts.prefixOperator bangTk f .withoutSpacingIfAtomic
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.Grind.grindFilter]
public def fmtGrindFilter : Fmt := fun
  | `(Parser.Tactic.Grind.grindFilter| $[$f?:grind_filter]?) => fmt? f?
  | _ => throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.Grind.grind_ref_]
public def fmtGrindRefAnchor : Fmt := fun
  | `(grind_ref| $a:anchor) => fmt a
  | _ => throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.Grind.«grind_ref__/__»]
public def fmtGrindRefAnchordOrd : Fmt := fun
  | `(Parser.Tactic.Grind.«grind_ref__/__»| $a/%$slashTk$n) => do
    let a ← fmt a
    let slashTk ← fmt slashTk
    let n ← fmt n
    return Layouts.atomicInfixOperator #[a, slashTk, n]
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.Grind.grind_ref__1]
public def fmtGrindRefTerm : Fmt := fun
  | `(grind_ref| $t:term) => fmt t
  | _ => throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.Grind.grindStep]
public def fmtGrindStep : Fmt := fun
  | `(Parser.Tactic.Grind.grindStep| $g:grind $[|%$pipeTk? $[$f?:grind_filter]?]?) => do
    let g ← fmt g
    let pipeTk? ← fmt? pipeTk?
    let f? ← fmt? f?.join
    let filter? := nested <| Layouts.softSpacedAtomic #[pipeTk?, f?]
    return maybeFlattened <| combine #[
      .withSepAfter g ⟨nl, nested⟩,
      filter?
    ]
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.Grind.grindSeq1Indented]
public def fmtGrindSeq1Indented : Fmt := fun
  | `(Parser.Tactic.Grind.grindSeq1Indented| $steps:grindStep;*) => do fmtSeq steps none
  | _ => throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.Grind.grindSeqBracketed]
public def fmtGrindSeqBracketed : Fmt := fun
  | `(Parser.Tactic.Grind.grindSeqBracketed|
      {%$lbTk
        $steps:grindStep;*
      }%$rbTk ) => do
    let lbTk ← fmt lbTk
    let steps ← fmtSeq steps none
    let rbTk ← fmt rbTk
    return Layouts.bracketed lbTk steps rbTk <| .sparse hardNl
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.Grind.grindSeq]
public def fmtGrindSeq : Fmt := fun
  | `(Parser.Tactic.Grind.grindSeq| $s:grindSeq1Indented) => fmt s
  | `(Parser.Tactic.Grind.grindSeq| $s:grindSeqBracketed) => fmt s
  | _ => throw .partialFormatter

public def fmtGrindKeywordFilter (tk : Syntax) (f : TSyntax ``Parser.Tactic.Grind.grindFilter)
    : FmtM TaggedDoc := do
  let tk ← fmt tk
  let f ← fmt f
  return Layouts.pseudoApplication #[tk, f]

@[builtin_fmt Lean.Parser.Tactic.Grind.showAsserted]
public def fmtGrindShowAsserted : Fmt := fun
  | `(grind| show_asserted%$tk $f:grindFilter) => fmtGrindKeywordFilter tk f
  | _ => throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.Grind.showTrue]
public def fmtGrindShowTrue : Fmt := fun
  | `(grind| show_true%$tk $f:grindFilter) => fmtGrindKeywordFilter tk f
  | _ => throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.Grind.showFalse]
public def fmtGrindShowFalse : Fmt := fun
  | `(grind| show_false%$tk $f:grindFilter) => fmtGrindKeywordFilter tk f
  | _ => throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.Grind.showEqcs]
public def fmtGrindShowEqcs : Fmt := fun
  | `(grind| show_eqcs%$tk $f:grindFilter) => fmtGrindKeywordFilter tk f
  | _ => throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.Grind.showCases]
public def fmtGrindShowCases : Fmt := fun
  | `(grind| show_cases%$tk $f:grindFilter) => fmtGrindKeywordFilter tk f
  | _ => throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.Grind.showState]
public def fmtGrindShowState : Fmt := fun
  | `(grind| show_state%$tk $f:grindFilter) => fmtGrindKeywordFilter tk f
  | _ => throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.Grind.casesTrace]
public def fmtGrindCasesTrace : Fmt := fun
  | `(grind| cases?%$tk $f:grindFilter) => fmtGrindKeywordFilter tk f
  | _ => throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.Grind.showTerm]
public def fmtGrindShowTerm : Fmt := fun
  | `(grind| show_term%$tk $s:grindSeq) => do
    let tk ← fmt tk
    let s ← fmt s
    return Layouts.keywordPrefixedSeq tk s .nonSticky
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.Grind.cases]
public def fmtGrindTacticCases : Fmt := fun
  | `(grind| cases%$tk $r:grind_ref) => do
    let tk ← fmt tk
    let r ← fmt r
    return Layouts.pseudoApplication #[tk, r]
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.Grind.withAnnotateState]
public def fmtGrindWithAnnotateState : Fmt := fun stx => do
  let tk ← getStxArg! stx 0
  let raw ← getStxArg! stx 1
  let g ← getStxArg! stx 2
  let tk ← fmt tk
  let raw ← fmt raw
  let g ← fmt g
  return Layouts.pseudoApplication #[tk, raw, g]

@[builtin_fmt Lean.Parser.Tactic.Grind.fail]
public def fmtGrindFail : Fmt := fun
  | `(grind| fail%$tk $[$msg?:str]?) => do
    let tk ← fmt tk
    let msg? ← fmt? msg?
    return Layouts.pseudoApplication #[tk, msg?]
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.Grind.renameI]
public def fmtGrindRenameI : Fmt := fun
  | `(grind| rename_i%$tk $args:binderIdent*) => do
    let tk ← fmt tk
    let args ← fmtArray args
    return Layouts.pseudoApplication <| #[tk] ++ args
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.Grind.symApply]
public def fmtGrindApply : Fmt := fun
  | `(grind| apply%$tk $e:term) => do
    let tk ← fmt tk
    let e ← fmt e
    return Layouts.pseudoApplication #[tk, e]
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.Grind.symInternalize]
public def fmtGrindInternalize : Fmt := fun
  | `(grind| internalize%$tk $[$n?:num]?) => do
    let tk ← fmt tk
    let n? ← fmt? n?
    return Layouts.pseudoApplication #[tk, n?]
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.Grind.grindExact_]
public def fmtGrindExact : Fmt := fun
  | `(grind| exact%$tk $e:term) => do
    let tk ← fmt tk
    let e ← fmt e
    return Layouts.pseudoApplication #[tk, e]
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.Grind.instantiate]
public def fmtGrindInstantiate : Fmt := fun
  | `(grind| instantiate%$tk $[only%$only?]? $[approx%$approx?]? $[[%$lbTk? $thms?:thm,* ]%$rbTk?]?) =>
    do
      let tk ← fmt tk
      let only? ← fmt? only?
      let approx? ← fmt? approx?
      let lbTk? ← fmt? lbTk?
      let thms ← fmtTSepArray (thms?.getD ⟨#[]⟩)
      let rbTk? ← fmt? rbTk?
      let keywords := Layouts.spacedAtomic #[tk, only?, approx?]
      let thms := Layouts.collection lbTk? thms rbTk?
      return Layouts.pseudoApplication #[keywords, thms]
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.Grind.use]
public def fmtGrindUse : Fmt := fun
  | `(grind| use%$tk [%$lbTk $thms:thm,* ]%$rbTk) => do
    let tk ← fmt tk
    let lbTk ← fmt lbTk
    let thms ← fmtTSepArray thms
    let rbTk ← fmt rbTk
    let thms := Layouts.collection lbTk thms rbTk
    return Layouts.pseudoApplication #[tk, thms]
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.Grind.finish]
public def fmtGrindFinish : Fmt := fun
  | `(grind| finish%$tk $cfgItems:configItem* $[only%$only?]? $[[%$lbTk? $args?:grindParam,* ]%$rbTk?]?) =>
    fmtSimpLikeWithGenericConfig #[tk] cfgItems none only? lbTk? args? rbTk? none
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.Grind.finishTrace]
public def fmtGrindFinishTrace : Fmt := fun
  | `(grind| finish?%$tk $cfgItems:configItem* $[only%$only?]? $[[%$lbTk? $args?:grindParam,* ]%$rbTk?]?) =>
    fmtSimpLikeWithGenericConfig #[tk] cfgItems none only? lbTk? args? rbTk? none
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.Grind.«have»]
public def fmtGrindHave : Fmt := fun
  | `(grind| have%$haveTk $decl:letDecl) => do
    let haveTk ← fmt haveTk
    let decl ← fmt decl
    return Layouts.letDecl haveTk empty decl
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.Grind.haveSilent]
public def fmtGrindHaveSilent : Fmt := fun
  | `(grind| have%$haveTk $[$id?:ident]? :%$colonTk $t:term) => do
    let haveTk ← fmt haveTk
    let id? ← fmt? id?
    let colonTk ← fmt colonTk
    let t ← fmt t
    return Layouts.localSignature #[haveTk, id?] #[] colonTk t
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.Grind.nestedTacticCore]
public def fmtGrindNestedTacticCore : Fmt := fun
  | `(grind| tactic%$tacticTk =>%$arrowTk $tac:tacticSeq) => do
    let tacticTk ← fmt tacticTk
    let arrowTk ← fmt arrowTk
    let tac ← fmt tac
    return Layouts.assignmentDeclaration tacticTk arrowTk tac
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.Grind.allGoals]
public def fmtGrindAllGoals : Fmt := fun
  | `(grind| all_goals%$tk $seq:grindSeq) => do
    let tk ← fmt tk
    let seq ← fmt seq
    return Layouts.keywordPrefixedSeq tk seq .nonSticky
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.Grind.case]
public def fmtGrindCase : Fmt := fun
  | `(grind| case%$caseTk $args:caseArg|* =>%$arrowTk $seq:grindSeq) =>
    fmtCaseDeclaration caseTk args arrowTk seq
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.Grind.anyGoals]
public def fmtGrindAnyGoals : Fmt := fun
  | `(grind| any_goals%$tk $seq:grindSeq) => do
    let tk ← fmt tk
    let seq ← fmt seq
    return Layouts.keywordPrefixedSeq tk seq .nonSticky
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.Grind.focus]
public def fmtGrindFocus : Fmt := fun
  | `(grind| focus%$tk $seq:grindSeq) => do
    let tk ← fmt tk
    let seq ← fmt seq
    return Layouts.keywordPrefixedSeq tk seq .nonSticky
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.Grind.failIfSuccess]
public def fmtGrindFailIfSuccess : Fmt := fun
  | `(grind| fail_if_success%$tk $seq:grindSeq) => do
    let tk ← fmt tk
    let seq ← fmt seq
    return Layouts.keywordPrefixedSeq tk seq .nonSticky
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.Grind.grindTry_]
public def fmtGrindTry : Fmt := fun
  | `(grind| try%$tk $seq:grindSeq) => do
    let tk ← fmt tk
    let seq ← fmt seq
    return Layouts.keywordPrefixedSeq tk seq .nonSticky
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.Grind.grindRepeat_]
public def fmtGrindRepeat : Fmt := fun
  | `(grind| repeat%$tk $seq:grindSeq) => do
    let tk ← fmt tk
    let seq ← fmt seq
    return Layouts.keywordPrefixedSeq tk seq .nonSticky
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.Grind.next]
public def fmtGrindNext : Fmt := fun
  | `(grind| next%$nextTk $args:binderIdent* =>%$arrowTk $seq:grindSeq) =>
    fmtNextLike nextTk args arrowTk seq
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.Grind.«grind·_»]
public def fmtGrindDot : Fmt := fun
  | `(grind| ·%$dotTk $s:grindSeq) => do
    let dotTk ← fmt dotTk
    let s ← fmt s
    return nested <| Layouts.softSpacedAtomic #[dotTk, s]
  | _ =>
    throw .partialFormatter

@[builtin_infix_fmt Lean.Parser.Tactic.Grind.«grind_<;>_»]
public def fmtGrindSeqFocus : Fmt.InfixOperation := {
  sparse := false
  precs? := some { prec := 1, lhsPrec := 0, rhsPrec := 2 }
}

@[builtin_fmt Lean.Parser.Tactic.Grind.first]
public def fmtGrindFirst : Fmt := fun
  | `(grind| first%$firstTk $[(%$lbTks $seqs:grindSeq )%$rbTks]*) => do
    let firstTk ← fmt firstTk
    let alts ←
      (lbTks.zip (seqs.zip rbTks)).mapM fun (lbTk, seq, rbTk) => do
        let lbTk ← fmt lbTk
        let seq ← fmt seq
        let rbTk ← fmt rbTk
        return Layouts.parens lbTk seq rbTk
    return nested <| Layouts.horizontalOrVertical (#[firstTk] ++ alts)
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.Grind.paren]
public def fmtGrindParen : Fmt := fun
  | `(grind| (%$lbTk $seq:grindSeq )%$rbTk) => do
    let lbTk ← fmt lbTk
    let seq ← fmt seq
    let rbTk ← fmt rbTk
    return Layouts.parenthesizedSeq lbTk seq rbTk
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.Grind.setOption]
public def fmtGrindSetOption : Fmt := fun
  | `(grind| set_option%$setOptionTk $idHead:ident $[.%$dotTk?$idTail?:ident]? $val in%$inTk $seq:grindSeq) =>
    do
      let setOptionTk ← fmt setOptionTk
      let idHead ← fmt idHead
      let dotTk? ← fmt? dotTk?
      let idTail? ← fmt? idTail?
      let val ← fmt val
      let inTk ← fmt inTk
      let seq ← fmt seq
      let optionId := Layouts.atomic #[idHead, dotTk?, idTail?]
      let setOption := Layouts.pseudoApplication #[setOptionTk, optionId, val]
      let indentedVariant :=
        Layouts.keywordSeparated setOption inTk seq { allowFlattening := false, nestedRhs := true }
      let dedentedVariant :=
        Layouts.keywordSeparated setOption inTk seq { allowFlattening := false, nestedRhs := false }
      return pseudoDedented indentedVariant dedentedVariant
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.Grind.setConfig]
public def fmtGrindSetConfig : Fmt := fun
  | `(grind| set_config%$setConfigTk $cfgItems:configItem* in%$inTk $seq:grindSeq) => do
    let setConfigTk ← fmt setConfigTk
    let cfgItems ← fmtArray cfgItems
    let setConfig := Layouts.pseudoApplication <| #[setConfigTk] ++ cfgItems
    let inTk ← fmt inTk
    let seq ← fmt seq
    let indentedVariant :=
      Layouts.keywordSeparated setConfig inTk seq { allowFlattening := false, nestedRhs := true }
    let dedentedVariant :=
      Layouts.keywordSeparated setConfig inTk seq { allowFlattening := false, nestedRhs := false }
    return pseudoDedented indentedVariant dedentedVariant
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.Grind.symIntro]
public def fmtGrindSymIntro : Fmt := fun
  | `(grind| intro%$introTk $[(%$lbTk? internalize%$intTk? :=%$ceqTk? $bVal? )%$rbTk?]? $ids:binderIdent*) =>
    do
      let introTk ← fmt introTk
      -- The `true`/`false` value is a `token.true`/`token.false` node; descend to its atom so we
      -- don't recurse into a node without a formatter.
      let namedArg ← fmtNamedArgumentTerm? lbTk? intTk? ceqTk? (bVal?.map (·.raw.getArg 0)) rbTk?
      let «intro» := Layouts.pseudoApplication <| #[introTk, namedArg]
      let ids ← fmtArray ids
      return Layouts.pseudoApplication <| #[«intro»] ++ ids
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.Grind.symIntroLight]
public def fmtGrindSymIntroLight : Fmt := fun
  | `(grind| intro%$introTk~%$tildeTk $ids:binderIdent*) => do
    let introTk ← fmt introTk
    let tildeTk ← fmt tildeTk
    let head := Layouts.atomic #[introTk, tildeTk]
    let ids ← fmtArray ids
    return Layouts.pseudoApplication <| #[head] ++ ids
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.Grind.symIntros]
public def fmtGrindSymIntros : Fmt := fun
  | `(grind| intros%$introsTk $[(%$lbTk? internalize%$intTk? :=%$ceqTk? $bVal? )%$rbTk?]?) => do
    let introsTk ← fmt introsTk
    -- The `true`/`false` value is a `token.true`/`token.false` node; descend to its atom so we
    -- don't recurse into a node without a formatter.
    let namedArg ← fmtNamedArgumentTerm? lbTk? intTk? ceqTk? (bVal?.map (·.raw.getArg 0)) rbTk?
    return Layouts.pseudoApplication #[introsTk, namedArg]
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.Grind.symIntrosLight]
public def fmtGrindSymIntrosLight : Fmt := fun
  | `(grind| intros%$introsTk~%$tildeTk) => do
    let introsTk ← fmt introsTk
    let tildeTk ← fmt tildeTk
    return Layouts.atomic #[introsTk, tildeTk]
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.Grind.symSimp]
public def fmtGrindSimp : Fmt := fun
  | `(grind| simp%$simpTk $[$variant?:ident]? $[[%$lbTk? $thms?:ident,* ]%$rbTk?]?) => do
    let simpTk ← fmt simpTk
    let variant? ← fmt? variant?
    let lbTk? ← fmt? lbTk?
    let thms ← fmtTSepArray (thms?.getD ⟨#[]⟩)
    let rbTk? ← fmt? rbTk?
    let thms := Layouts.collection lbTk? thms rbTk?
    return Layouts.pseudoApplication #[simpTk, variant?, thms]
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.Grind.symDSimp]
public def fmtGrindDSimp : Fmt := fun
  | `(grind| dsimp%$dsimpTk $[$variant?:ident]? $[[%$lbTk? $thms?,* ]%$rbTk?]?) => do
    let dsimpTk ← fmt dsimpTk
    let variant? ← fmt? variant?
    let lbTk? ← fmt? lbTk?
    let fmtStarOrIdent : Fmt := fun e => if e.isIdent then fmt e else fmtAtomic e
    let thms ← fmtTSepArrayWith fmtStarOrIdent `fmtStarOrIdent (thms?.getD ⟨#[]⟩)
    let rbTk? ← fmt? rbTk?
    let thms := Layouts.collection lbTk? thms rbTk?
    return Layouts.pseudoApplication #[dsimpTk, variant?, thms]
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.Grind.symRw]
public def fmtGrindRw : Fmt := fun
  | `(grind| rw%$rwTk $rules:rwRuleSeq) => fmtRwLike rwTk none rules none
  | _ => throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.Grind.bvNormalize]
public def fmtGrindBvNormalize : Fmt := fun
  | `(grind| bv_normalize%$bvNormalizeTk $cfg:optConfig $[$types?:bvTypes]?) => do
    let bvNormalizeTk ← fmt bvNormalizeTk
    let cfg ← (← tacticOptConfigItems cfg).mapM fmt
    let types? ← fmt? types?
    let lhs := Layouts.pseudoApplication <| #[bvNormalizeTk] ++ cfg
    return Layouts.blocks #[lhs, types?]
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.Grind.bvDecide]
public def fmtGrindBvDecide : Fmt := fun
  | `(grind| bv_decide%$bvDecideTk $cfg:optConfig $[$types?:bvTypes]?) => do
    let bvDecideTk ← fmt bvDecideTk
    let cfg ← (← tacticOptConfigItems cfg).mapM fmt
    let types? ← fmt? types?
    let lhs := Layouts.pseudoApplication <| #[bvDecideTk] ++ cfg
    return Layouts.blocks #[lhs, types?]
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.Grind.bvTrace]
public def fmtGrindBvTrace : Fmt := fun
  | `(grind| bv_decide?%$bvTraceTk $cfg:optConfig $[$types?:bvTypes]?) => do
    let bvTraceTk ← fmt bvTraceTk
    let cfg ← (← tacticOptConfigItems cfg).mapM fmt
    let types? ← fmt? types?
    let lhs := Layouts.pseudoApplication <| #[bvTraceTk] ++ cfg
    return Layouts.blocks #[lhs, types?]
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.Grind.bvCheck]
public def fmtGrindBvCheck : Fmt := fun
  | `(grind| bv_check%$bvCheckTk $cfg:optConfig $[$types?:bvTypes]? $lratFile:str) => do
    let bvCheckTk ← fmt bvCheckTk
    let cfg ← (← tacticOptConfigItems cfg).mapM fmt
    let types? ← fmt? types?
    let lratFile ← fmt lratFile
    let lhs := Layouts.pseudoApplication <| #[bvCheckTk] ++ cfg
    return Layouts.blocks #[lhs, types?, lratFile]
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.Grind.bvDecidePush]
public def fmtGrindBvDecidePush : Fmt := fun
  | `(grind| bv_decide_push%$bvDecidePushTk $cfg:optConfig) => do
    let bvDecidePushTk ← fmt bvDecidePushTk
    let cfg ← (← tacticOptConfigItems cfg).mapM fmt
    return Layouts.pseudoApplication <| #[bvDecidePushTk] ++ cfg
  | _ =>
    throw .partialFormatter
