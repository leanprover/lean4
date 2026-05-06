/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Marc Huisinga
-/
module

prelude
public import Lean.Fmt.FmtM.Basic
public import Lean.Fmt.Formatters.Lean.Parser.Term
meta import Init.Tactics
import Lean.Fmt.FmtM.CommonFormatters
import Init.Data

namespace Lean.Fmt

@[builtin_fmt Lean.Parser.Tactic.posConfigItem]
public def fmtTacticPosConfigItem : Fmt := fun
  | `(Parser.Tactic.posConfigItem| +%$plusTk$id:ident) => do
    let plusTk ← fmt plusTk
    let id ← fmt id
    return Layouts.atomic #[plusTk, id]
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.negConfigItem]
public def fmtTacticNegConfigItem : Fmt := fun
  | `(Parser.Tactic.negConfigItem| -%$minusTk$id:ident) => do
    let minusTk ← fmt minusTk
    let id ← fmt id
    return Layouts.atomic #[minusTk, id]
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.valConfigItem]
public def fmtTacticValConfigItem : Fmt := fun
  | `(Parser.Tactic.valConfigItem| (%$lbTk $id:ident :=%$colonEqTk $body:term )%$rbTk) =>
    fmtNamedArgumentTerm lbTk id colonEqTk body rbTk
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.config]
public def fmtTacticConfig : Fmt := fun
  | `(Parser.Tactic.config| (%$lbTk config%$configTk :=%$colonEqTk $body:term )%$rbTk) =>
    fmtNamedArgumentTerm lbTk configTk colonEqTk body rbTk
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.discharger]
public def fmtTacticDischarger : Fmt := fun stx => do
  let lbTk ← getStxArg! stx 0
  let kwNode ← getStxArg! stx 1
  let kwTk ← getStxArg! (← getStxArg! kwNode 0) 0
  let colonEqTk ← getStxArg! stx 2
  let body ← getStxArg! stx 3
  let rbTk ← getStxArg! stx 4
  fmtNamedArgumentTerm lbTk kwTk colonEqTk body rbTk

@[builtin_fmt Lean.Parser.Tactic.configItem]
public def fmtTacticConfigItem : Fmt := fun
  | `(Parser.Tactic.configItem| $item:posConfigItem) => fmt item
  | `(Parser.Tactic.configItem| $item:negConfigItem) => fmt item
  | `(Parser.Tactic.configItem| $item:valConfigItem) => fmt item
  | _ => throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.location]
public def fmtLocation : Fmt := fun stx => do
  let atTk ← getStxArg! stx 0
  let rest ← getStxArg! stx 1
  if rest.getKind == ``Parser.Tactic.locationWildcard then
    let atTk ← fmt atTk
    let rest ← fmt rest
    return withPosition <|
      Layouts.pseudoApplication (format := { parenthesize := true }) #[atTk, rest]
  else if rest.getKind == ``Parser.Tactic.locationHyp then
    let atTk ← fmt atTk
    let targets ← (← getStxArg! rest 0).getArgs.mapM fmt
    return withPosition <| Layouts.pseudoApplication (format := { parenthesize := true }) <|
      #[atTk] ++ targets
  else
    throw .partialFormatter

public def fmtWithLocationSuffix
    (lhs : TaggedDoc) (suffix? : Option (TSyntax ``Parser.Tactic.location))
    : FmtM TaggedDoc := do
  let suffix? ← fmt? suffix?
  return Layouts.pseudoApplication #[lhs, suffix?]

@[builtin_fmt Lean.Parser.Tactic.withAnnotateState]
public def fmtWithAnnotateState : Fmt := fun stx => do
  let withAnnotateStateTk ← getStxArg! stx 0
  let rawStx ← getStxArg! stx 1
  let tactic ← getStxArg! stx 2
  let withAnnotateStateTk ← fmt withAnnotateStateTk
  let rawStx ← fmt rawStx
  let tactic ← fmt tactic
  return Layouts.pseudoApplication #[withAnnotateStateTk, rawStx, tactic]

@[builtin_fmt Lean.Parser.Tactic.intro]
public def fmtIntro : Fmt := fun
  | `(tactic| intro%$introTk $args:term*) => do
    let introTk ← fmt introTk
    let args ← fmtArray args
    return Layouts.pseudoApplication (format := { parenthesize := true }) <| #[introTk] ++ args
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.intros]
public def fmtIntros : Fmt := fun
  | `(tactic| intros%$introsTk $args*) => do
    let introsTk ← fmt introsTk
    let args ← fmtArray args
    return Layouts.pseudoApplication <| #[introsTk] ++ args
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.revert]
public def fmtRevert : Fmt := fun
  | `(tactic| revert%$revertTk $args:term*) => do
    let revertTk ← fmt revertTk
    let args ← fmtArray args
    return Layouts.pseudoApplication (format := { parenthesize := true }) <| #[revertTk] ++ args
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.clear]
public def fmtTacticClear : Fmt := fun stx => do
  let `(tactic| clear $args:term*) := stx
    | throw .partialFormatter
  let clearTk ← fmt (← getStxArg! stx 0)
  let args ← fmtArray args
  return Layouts.pseudoApplication (format := { parenthesize := true }) <| #[clearTk] ++ args

@[builtin_fmt Lean.Parser.Tactic.clearValue]
public def fmtClearValue : Fmt := fun
  | `(tactic| clear_value%$clearValueTk $args:clearValueArg*) => do
    let clearValueTk ← fmt clearValueTk
    let args ← fmtArray args
    return Layouts.pseudoApplication (format := { parenthesize := true }) <| #[clearValueTk] ++ args
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.subst]
public def fmtTacticSubst : Fmt := fun
  | `(tactic| subst%$substTk $args:term*) => do
    let substTk ← fmt substTk
    let args ← fmtArray args
    return Layouts.pseudoApplication (format := { parenthesize := true }) <| #[substTk] ++ args
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.apply]
public def fmtApply : Fmt := fun
  | `(tactic| apply%$applyTk $e:term) => do
    let applyTk ← fmt applyTk
    let e ← fmt e
    return Layouts.pseudoApplication #[applyTk, e]
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.exact]
public def fmtExact : Fmt := fun
  | `(tactic| exact%$exactTk $e:term) => do
    let exactTk ← fmt exactTk
    let e ← fmt e
    return Layouts.pseudoApplication #[exactTk, e]
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.refine]
public def fmtRefine : Fmt := fun
  | `(tactic| refine%$refineTk $e:term) => do
    let refineTk ← fmt refineTk
    let e ← fmt e
    return Layouts.pseudoApplication #[refineTk, e]
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.refine']
public def fmtRefine' : Fmt := fun
  | `(tactic| refine'%$refineTk $e:term) => do
    let refineTk ← fmt refineTk
    let e ← fmt e
    return Layouts.pseudoApplication #[refineTk, e]
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.constructor]
public def fmtConstructor : Fmt := fun
  | `(tactic| constructor%$constructorTk $cfg:optConfig) => do
    let constructorTk ← fmt constructorTk
    let cfg ← (← tacticOptConfigItems cfg).mapM fmt
    return Layouts.pseudoApplication <| #[constructorTk] ++ cfg
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.constructorBang]
public def fmtConstructorBang : Fmt := fun
  | `(tactic| constructor!%$constructorTk $cfg:optConfig) => do
    let constructorTk ← fmt constructorTk
    let cfg ← (← tacticOptConfigItems cfg).mapM fmt
    return Layouts.pseudoApplication <| #[constructorTk] ++ cfg
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.traceMessage]
public def fmtTrace : Fmt := fun
  | `(tactic| trace%$traceTk $msg:str) => do
    let traceTk ← fmt traceTk
    let msg ← fmt msg
    return Layouts.pseudoApplication #[traceTk, msg]
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.rotateLeft]
public def fmtRotateLeft : Fmt := fun
  | `(tactic| rotate_left%$rotateTk $[$n?:num]?) => do
    let rotateTk ← fmt rotateTk
    let n? ← fmt? n?
    return Layouts.pseudoApplication #[rotateTk, n?]
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.rotateRight]
public def fmtRotateRight : Fmt := fun
  | `(tactic| rotate_right%$rotateTk $[$n?:num]?) => do
    let rotateTk ← fmt rotateTk
    let n? ← fmt? n?
    return Layouts.pseudoApplication #[rotateTk, n?]
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.fail]
public def fmtFail : Fmt := fun
  | `(tactic| fail%$failTk $[$msg?:str]?) => do
    let failTk ← fmt failTk
    let msg? ← fmt? msg?
    return Layouts.pseudoApplication #[failTk, msg?]
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.injections]
public def fmtInjections : Fmt := fun
  | `(tactic| injections%$injectionsTk $args*) => do
    let injectionsTk ← fmt injectionsTk
    let args ← fmtArray args
    return Layouts.pseudoApplication <| #[injectionsTk] ++ args
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.tacticRefine_lift_]
public def fmtRefineLift : Fmt := fun
  | `(tactic| refine_lift%$refineLiftTk $e:term) => do
    let refineLiftTk ← fmt refineLiftTk
    let e ← fmt e
    return Layouts.pseudoApplication #[refineLiftTk, e]
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.tacticRefine_lift'_]
public def fmtRefineLift' : Fmt := fun
  | `(tactic| refine_lift'%$refineLiftTk $e:term) => do
    let refineLiftTk ← fmt refineLiftTk
    let e ← fmt e
    return Layouts.pseudoApplication #[refineLiftTk, e]
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.renameI]
public def fmtRenameI : Fmt := fun
  | `(tactic| rename_i%$renameTk $args:binderIdent*) => do
    let renameTk ← fmt renameTk
    let args ← fmtArray args
    return Layouts.pseudoApplication <| #[renameTk] ++ args
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.dbgTrace]
public def fmtTacticDbgTrace : Fmt := fun
  | `(tactic| dbg_trace%$dbgTraceTk $msg:str) => do
    let dbgTraceTk ← fmt dbgTraceTk
    let msg ← fmt msg
    return Layouts.pseudoApplication #[dbgTraceTk, msg]
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.sleep]
public def fmtSleep : Fmt := fun
  | `(tactic| sleep%$sleepTk $n:num) => do
    let sleepTk ← fmt sleepTk
    let n ← fmt n
    return Layouts.pseudoApplication #[sleepTk, n]
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.congr]
public def fmtCongr : Fmt := fun
  | `(tactic| congr%$congrTk $[$n?:num]?) => do
    let congrTk ← fmt congrTk
    let n? ← fmt? n?
    return Layouts.pseudoApplication #[congrTk, n?]
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.specialize]
public def fmtSpecialize : Fmt := fun
  | `(tactic| specialize%$specializeTk $e:term) => do
    let specializeTk ← fmt specializeTk
    let e ← fmt e
    return Layouts.pseudoApplication #[specializeTk, e]
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.normCastAddElim]
public def fmtNormCastAddElim : Fmt := fun
  | `(Parser.Tactic.normCastAddElim| norm_cast_add_elim%$normCastTk $id:ident) => do
    let normCastTk ← fmt normCastTk
    let id ← fmt id
    return Layouts.pseudoApplication #[normCastTk, id]
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.showTermElab]
public def fmtShowTermElab : Fmt := fun
  | `(Parser.Tactic.showTermElab| show_term%$showTermTk $e:term) => do fmtAppLike #[showTermTk, e]
  | _ => throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.as_aux_lemma]
public def fmtAsAuxLemma : Fmt := fun
  | `(tactic| as_aux_lemma%$asAuxLemmaTk =>%$arrowTk $tac:tacticSeq) => do
    let asAuxLemmaTk ← fmt asAuxLemmaTk
    let arrowTk ← fmt arrowTk
    let tac ← fmt tac
    return Layouts.assignmentDeclaration asAuxLemmaTk arrowTk tac
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.rename]
public def fmtRename : Fmt := fun
  | `(tactic| rename%$renameTk $t:term =>%$arrowTk $id:ident) => do
    let renameTk ← fmt renameTk
    let t ← fmt t
    let lhs := Layouts.pseudoApplication #[renameTk, t]
    let arrowTk ← fmt arrowTk
    let id ← fmt id
    return Layouts.assignmentDeclaration lhs arrowTk id
  | _ =>
    throw .partialFormatter

public def fmtNextLike
    (nextTk : Syntax) (args : Array (TSyntax k)) (arrowTk : Syntax) (tac : Syntax)
    : FmtM TaggedDoc := do
  let nextTk ← fmt nextTk
  let args ← fmtArray args
  let lhs := Layouts.pseudoApplication <| #[nextTk] ++ args
  let arrowTk ← fmt arrowTk
  let tac ← fmt tac
  return Layouts.assignmentDeclaration lhs arrowTk tac

@[builtin_fmt Lean.Parser.Tactic.«tacticNext_=>_»]
public def fmtNext : Fmt := fun
  | `(tactic| next%$nextTk $args:binderIdent* =>%$arrowTk $tac:tacticSeq) =>
    fmtNextLike nextTk args arrowTk tac
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.allGoals]
public def fmtAllGoals : Fmt := fun
  | `(tactic| all_goals%$allGoalsTk $tac:tacticSeq) => do
    let allGoalsTk ← fmt allGoalsTk
    let tac ← fmt tac
    return Layouts.keywordPrefixedSeq allGoalsTk tac .nonSticky
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.anyGoals]
public def fmtAnyGoals : Fmt := fun
  | `(tactic| any_goals%$anyGoalsTk $tac:tacticSeq) => do
    let anyGoalsTk ← fmt anyGoalsTk
    let tac ← fmt tac
    return Layouts.keywordPrefixedSeq anyGoalsTk tac .nonSticky
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.focus]
public def fmtFocus : Fmt := fun
  | `(tactic| focus%$focusTk $tac:tacticSeq) => do
    let focusTk ← fmt focusTk
    let tac ← fmt tac
    return Layouts.keywordPrefixedSeq focusTk tac .nonSticky
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.failIfSuccess]
public def fmtFailIfSuccess : Fmt := fun
  | `(tactic| fail_if_success%$failTk $tac:tacticSeq) => do
    let failTk ← fmt failTk
    let tac ← fmt tac
    return Layouts.keywordPrefixedSeq failTk tac .nonSticky
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.withReducible]
public def fmtWithReducible : Fmt := fun
  | `(tactic| with_reducible%$withReducibleTk $tac:tacticSeq) => do
    let withReducibleTk ← fmt withReducibleTk
    let tac ← fmt tac
    return Layouts.keywordPrefixedSeq withReducibleTk tac .nonSticky
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.withReducibleAndInstances]
public def fmtWithReducibleAndInstances : Fmt := fun
  | `(tactic| with_reducible_and_instances%$withReducibleTk $tac:tacticSeq) => do
    let withReducibleTk ← fmt withReducibleTk
    let tac ← fmt tac
    return Layouts.keywordPrefixedSeq withReducibleTk tac .nonSticky
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.withImplicit]
public def fmtWithImplicit : Fmt := fun
  | `(tactic| with_implicit%$withImplicitTk $tac:tacticSeq) => do
    let withImplicitTk ← fmt withImplicitTk
    let tac ← fmt tac
    return Layouts.keywordPrefixedSeq withImplicitTk tac .nonSticky
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.withUnfoldingAll]
public def fmtWithUnfoldingAll : Fmt := fun
  | `(tactic| with_unfolding_all%$withUnfoldingTk $tac:tacticSeq) => do
    let withUnfoldingTk ← fmt withUnfoldingTk
    let tac ← fmt tac
    return Layouts.keywordPrefixedSeq withUnfoldingTk tac .nonSticky
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.withUnfoldingNone]
public def fmtWithUnfoldingNone : Fmt := fun
  | `(tactic| with_unfolding_none%$withUnfoldingTk $tac:tacticSeq) => do
    let withUnfoldingTk ← fmt withUnfoldingTk
    let tac ← fmt tac
    return Layouts.keywordPrefixedSeq withUnfoldingTk tac .nonSticky
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.tacticTry_]
public def fmtTry : Fmt := fun
  | `(tactic| try%$tryTk $tac:tacticSeq) => do
    let tryTk ← fmt tryTk
    let tac ← fmt tac
    return Layouts.keywordPrefixedSeq tryTk tac .nonSticky
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.tacticRepeat_]
public def fmtRepeat : Fmt := fun
  | `(tactic| repeat%$repeatTk $tac:tacticSeq) => do
    let repeatTk ← fmt repeatTk
    let tac ← fmt tac
    return Layouts.keywordPrefixedSeq repeatTk tac .nonSticky
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.repeat']
public def fmtRepeat' : Fmt := fun
  | `(tactic| repeat'%$repeatTk $tac:tacticSeq) => do
    let repeatTk ← fmt repeatTk
    let tac ← fmt tac
    return Layouts.keywordPrefixedSeq repeatTk tac .nonSticky
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.repeat1']
public def fmtRepeat1' : Fmt := fun
  | `(tactic| repeat1'%$repeatTk $tac:tacticSeq) => do
    let repeatTk ← fmt repeatTk
    let tac ← fmt tac
    return Layouts.keywordPrefixedSeq repeatTk tac .nonSticky
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.runTac]
public def fmtRunTac : Fmt := fun
  | `(tactic| run_tac%$runTacTk $d:doSeq) => do
    let runTacTk ← fmt runTacTk
    let d ← fmt d
    return Layouts.keywordPrefixedSeq runTacTk d .nonSticky
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.showTerm]
public def fmtShowTerm : Fmt := fun
  | `(tactic| show_term%$showTermTk $tac:tacticSeq) => do
    let showTermTk ← fmt showTermTk
    let tac ← fmt tac
    return Layouts.keywordPrefixedSeq showTermTk tac .nonSticky
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.classical]
public def fmtClassical : Fmt := fun
  | `(tactic| classical%$classicalTk $tac:tacticSeq) => do
    let classicalTk ← fmt classicalTk
    let tac ← fmt tac
    let indentedVariant := Layouts.keywordPrefixedSeq classicalTk tac .nonSticky
    let dedentedVariant := Layouts.lines #[classicalTk, tac]
    return pseudoDedented indentedVariant dedentedVariant
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.tacticStop_]
public def fmtStop : Fmt := fun
  | `(tactic| stop%$stopTk $tac:tacticSeq) => do
    let stopTk ← fmt stopTk
    let tac ← fmt tac
    let indentedVariant := Layouts.keywordPrefixedSeq stopTk tac .nonSticky
    let dedentedVariant := Layouts.lines #[stopTk, tac]
    return pseudoDedented indentedVariant dedentedVariant
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.tacticUnhygienic_]
public def fmtUnhygienic : Fmt := fun
  | `(tactic| unhygienic%$unhygienicTk $tac:tacticSeq) => do
    let unhygienicTk ← fmt unhygienicTk
    let tac ← fmt tac
    let indentedVariant := Layouts.keywordPrefixedSeq unhygienicTk tac .nonSticky
    let dedentedVariant := Layouts.lines #[unhygienicTk, tac]
    return pseudoDedented indentedVariant dedentedVariant
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.first]
public def fmtFirst : Fmt := fun
  | `(tactic| first%$firstTk $[|%$barTks $tacticSeqs:tacticSeq]*) =>
    fmtAltsTactic firstTk barTks tacticSeqs
  | _ =>
    throw .partialFormatter

@[builtin_infix_fmt Lean.Parser.Tactic.«tactic_<;>_»]
public def fmtSeqFocus : Fmt.InfixOperation := {
  sparse := false
  precs? := some { prec := 1, lhsPrec := 0, rhsPrec := 2 }
}

@[builtin_fmt Lean.Parser.Tactic.paren]
public def fmtTacticParen : Fmt := fun
  | `(tactic| (%$lbTk $tac:tacticSeq )%$rbTk) => do
    let lbTk ← fmt lbTk
    let tac ← fmt tac
    let rbTk ← fmt rbTk
    return Layouts.parenthesizedSeq lbTk tac rbTk
  | _ =>
    throw .partialFormatter

public def fmtSimpAttrLike (tk : Syntax) (dir? revTk? prio? : Option Syntax) : FmtM TaggedDoc := do
  let tk ← fmt tk
  let dir? ← fmt? dir?
  let revTk? ← fmt? revTk?
  let prio? ← fmt? prio?
  let prio? :=
    Layouts.prefixOperator dir? (Layouts.prefixOperator revTk? prio? .withSpacing) .withSpacing
  return Layouts.pseudoApplication #[tk, prio?]

@[builtin_fmt Lean.Parser.Attr.simp]
public def fmtSimpAttr : Fmt := fun
  | `(Parser.Attr.simp| simp%$simpTk $[$dir?]? $[←%$revTk?]? $[$prio?:prio]?) =>
    fmtSimpAttrLike simpTk dir? revTk? prio?
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Attr.wf_preprocess]
public def fmtWfPreprocessAttr : Fmt := fun
  | `(Parser.Attr.wf_preprocess| wf_preprocess%$tk $[$dir?]? $[←%$revTk?]? $[$prio?:prio]?) =>
    fmtSimpAttrLike tk dir? revTk? prio?
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Attr.method_specs_simp]
public def fmtMethodSpecsSimpAttr : Fmt := fun
  | `(Parser.Attr.method_specs_simp| method_specs_simp%$tk $[$dir?]? $[←%$revTk?]? $[$prio?:prio]?) =>
    fmtSimpAttrLike tk dir? revTk? prio?
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.simpLemma]
public def fmtSimpLemma : Fmt := fun
  | `(Parser.Tactic.simpLemma| $[$dir?]? $[←%$revTk?]? $e:term) => do
    let dir? ← fmt? dir?
    let revTk? ← fmt? revTk?
    let e ← fmt e
    return Layouts.prefixOperator dir? (Layouts.prefixOperator revTk? e .withSpacing) .withSpacing
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.simpErase]
public def fmtSimpErase : Fmt := fun
  | `(Parser.Tactic.simpErase| -%$minusTk $e:term) => do
    let minusTk ← fmt minusTk
    let e ← fmt e
    return Layouts.prefixOperator minusTk e .withoutSpacingIfAtomic
  | _ =>
    throw .partialFormatter

public def fmtSimpaLike
    (lhs : TaggedDoc) (cfg : TSyntax ``Parser.Tactic.optConfig)
    (disch? : Option (TSyntax ``Parser.Tactic.discharger)) (only? : Option Syntax)
    (lbTk? : Option Syntax) (args? : Option (Syntax.SepArray ",")) (rbTk? : Option Syntax)
    (usingTk? : Option Syntax) (usingTerms? : SepArray ",")
    : FmtM TaggedDoc := do
  let cfgItems ← (← tacticOptConfigItems cfg).mapM fmt
  let disch? ← fmt? disch?
  let simpaLhs := Layouts.pseudoApplication <| #[lhs] ++ cfgItems ++ #[disch?]
  let onlyTk? ← fmt? only?
  let lbTk? ← fmt? lbTk?
  let args ← fmtSepArray (args?.getD ⟨#[]⟩)
  let rbTk? ← fmt? rbTk?
  let usingTk? ← fmt? usingTk?
  let args := Layouts.keywordPrefixedCollection onlyTk? lbTk? args rbTk?
  let «using» := Layouts.keywordPrefixedSepFill usingTk? usingTerms? .sticky
  return Layouts.blocks #[simpaLhs, args, «using»]

@[builtin_fmt Lean.Parser.Tactic.simp]
public def fmtSimp : Fmt := fun
  | `(tactic| simp%$simpTk $cfg:optConfig $[$disch:discharger]? $[only%$only?]?
      $[[%$lbTk? $args?,* ]%$rbTk?]? $[$loc?:location]?) => do
    fmtSimpLike #[simpTk] cfg disch only? lbTk? args? rbTk? loc?
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.simpAll]
public def fmtSimpAll : Fmt := fun
  | `(tactic| simp_all%$simpAllTk $cfg:optConfig $[$disch:discharger]? $[only%$only?]?
      $[[%$lbTk? $args?,* ]%$rbTk?]?) =>
    fmtSimpLike #[simpAllTk] cfg disch only? lbTk? args? rbTk? none
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.dsimp]
public def fmtDSimp : Fmt := fun
  | `(tactic| dsimp%$dsimpTk $cfg:optConfig $[$disch:discharger]? $[only%$only?]?
      $[[%$lbTk? $args?,* ]%$rbTk?]? $[$loc?:location]?) => do
    fmtSimpLike #[dsimpTk] cfg disch only? lbTk? args? rbTk? loc?
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.pushCast]
public def fmtPushCast : Fmt := fun
  | `(tactic| push_cast%$pushCastTk $cfg:optConfig $[$disch:discharger]? $[only%$only?]?
      $[[%$lbTk? $args?,* ]%$rbTk?]? $[$loc?:location]?) => do
    fmtSimpLike #[pushCastTk] cfg disch only? lbTk? args? rbTk? loc?
  | _ =>
    throw .partialFormatter

public def fmtWithSimpTraceArgsRest
    (lhs : Array Syntax) (rest : TSyntax ``Parser.Tactic.simpTraceArgsRest)
    : FmtM TaggedDoc := do
  match rest with
  | `(Parser.Tactic.simpTraceArgsRest|
      $cfg:optConfig $[$disch:discharger]? $[only%$only?]? $[[%$lbTk? $args?,* ]%$rbTk?]? $[$loc?:location]?) =>
    do fmtSimpLike lhs cfg disch only? lbTk? args? rbTk? loc?
  | _ =>
    throw .partialFormatter

public def fmtWithSimpAllTraceArgsRest
    (lhs : Array Syntax) (rest : TSyntax ``Parser.Tactic.simpAllTraceArgsRest)
    : FmtM TaggedDoc := do
  match rest with
  | `(Parser.Tactic.simpAllTraceArgsRest|
      $cfg:optConfig $[$disch:discharger]? $[only%$only?]? $[[%$lbTk? $args?,* ]%$rbTk?]?) =>
    fmtSimpLike lhs cfg disch only? lbTk? args? rbTk? none
  | _ =>
    throw .partialFormatter

public def fmtWithDSimpTraceArgsRest
    (lhs : Array Syntax) (rest : TSyntax ``Parser.Tactic.dsimpTraceArgsRest)
    : FmtM TaggedDoc := do
  match rest with
  | `(Parser.Tactic.dsimpTraceArgsRest|
      $cfg:optConfig $[only%$only?]? $[[%$lbTk? $args?,* ]%$rbTk?]? $[$loc?:location]?) => do
    fmtSimpLike lhs cfg none only? lbTk? args? rbTk? loc?
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.simpTrace]
public def fmtSimpTrace : Fmt := fun
  | `(tactic| simp?%$simpTk $[!%$bangTk?]? $rest:simpTraceArgsRest) =>
    fmtWithSimpTraceArgsRest (#[simpTk] ++ bangTk?.toArray) rest
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.«tacticSimp?!_»]
public def fmtSimpTraceBang : Fmt := fun
  | `(tactic| simp?!%$tk $rest:simpTraceArgsRest) => fmtWithSimpTraceArgsRest #[tk] rest
  | _ => throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.simpAllTrace]
public def fmtSimpAllTrace : Fmt := fun
  | `(tactic| simp_all?%$tk $[!%$bangTk?]? $rest:simpAllTraceArgsRest) =>
    fmtWithSimpAllTraceArgsRest (#[tk] ++ bangTk?.toArray) rest
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.«tacticSimp_all?!_»]
public def fmtSimpAllTraceBang : Fmt := fun
  | `(tactic| simp_all?!%$tk $rest:simpAllTraceArgsRest) => fmtWithSimpAllTraceArgsRest #[tk] rest
  | _ => throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.dsimpTrace]
public def fmtDSimpTrace : Fmt := fun
  | `(tactic| dsimp?%$tk $[!%$bangTk?]? $rest:dsimpTraceArgsRest) =>
    fmtWithDSimpTraceArgsRest (#[tk] ++ bangTk?.toArray) rest
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.«tacticDsimp?!_»]
public def fmtDSimpTraceBang : Fmt := fun
  | `(tactic| dsimp?!%$tk $rest:dsimpTraceArgsRest) => fmtWithDSimpTraceArgsRest #[tk] rest
  | _ => throw .partialFormatter

public def fmtWithSimpaArgsRest (lhs : Array Syntax) (rest : TSyntax ``Parser.Tactic.simpaArgsRest)
    : FmtM TaggedDoc := do
  match rest with
  | `(Parser.Tactic.simpaArgsRest|
      $cfg:optConfig $[$disch:discharger]? $[only%$only?]? $[[%$lbTk? $args?,* ]%$rbTk?]?
      $[using%$usingTk? $usingArg?:term]?) => do
    let usingArg? ← fmt? usingArg?
    let lhs ← lhs.mapM fmt
    let lhs := Layouts.spacedAtomic lhs
    fmtSimpaLike lhs cfg disch only? lbTk? args? rbTk? usingTk? ⟨#[usingArg?]⟩
  | _ =>
    throw .partialFormatter

public def fmtWithSimpaUsingBangArgsRest
    (lhs : Array Syntax) (rest : TSyntax ``Parser.Tactic.simpaUsingBangArgsRest)
    : FmtM TaggedDoc := do
  match rest with
  | `(Parser.Tactic.simpaUsingBangArgsRest|
      $cfg:optConfig $[$disch:discharger]? $[only%$only?]? $[[%$lbTk? $args?,* ]%$rbTk?]?
      using!%$usingTk $usingArg:term) => do
    let lhs ← lhs.mapM fmt
    let usingArg? ← fmt usingArg
    let lhs := Layouts.spacedAtomic lhs
    fmtSimpaLike lhs cfg disch only? lbTk? args? rbTk? usingTk ⟨#[usingArg?]⟩
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.simpa]
public def fmtSimpa : Fmt := fun
  | `(tactic| simpa%$simpaTk $[?%$questionTk?]? $[!%$bangTk?]? $rest:simpaArgsRest) =>
    fmtWithSimpaArgsRest (#[simpaTk] ++ questionTk?.toArray ++ bangTk?.toArray) rest
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.simpaUsingBang]
public def fmtSimpaUsingBang : Fmt := fun
  | `(tactic| simpa%$simpaTk $[?%$questionTk?]? $[!%$bangTk?]? $rest:simpaUsingBangArgsRest) =>
    fmtWithSimpaUsingBangArgsRest (#[simpaTk] ++ questionTk?.toArray ++ bangTk?.toArray) rest
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.«tacticSimpa!_»]
public def fmtSimpaBang : Fmt := fun
  | `(tactic| simpa!%$tk $rest:simpaArgsRest) => fmtWithSimpaArgsRest #[tk] rest
  | _ => throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.«tacticSimpa?_»]
public def fmtSimpaQuestion : Fmt := fun
  | `(tactic| simpa?%$tk $rest:simpaArgsRest) => fmtWithSimpaArgsRest #[tk] rest
  | _ => throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.«tacticSimpa?!_»]
public def fmtSimpaQuestionBang : Fmt := fun
  | `(tactic| simpa?!%$tk $rest:simpaArgsRest) => fmtWithSimpaArgsRest #[tk] rest
  | _ => throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.«tacticSimpa!__1»]
public def fmtSimpaBangUsingBang : Fmt := fun
  | `(tactic| simpa!%$tk $rest:simpaUsingBangArgsRest) => fmtWithSimpaUsingBangArgsRest #[tk] rest
  | _ => throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.«tacticSimpa?__1»]
public def fmtSimpaQuestionUsingBang : Fmt := fun
  | `(tactic| simpa?%$tk $rest:simpaUsingBangArgsRest) => fmtWithSimpaUsingBangArgsRest #[tk] rest
  | _ => throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.«tacticSimpa?!__1»]
public def fmtSimpaQuestionBangUsingBang : Fmt := fun
  | `(tactic| simpa?!%$tk $rest:simpaUsingBangArgsRest) => fmtWithSimpaUsingBangArgsRest #[tk] rest
  | _ => throw .partialFormatter

section
open Lean.Parser.Tactic.SolveByElim

@[builtin_fmt Lean.Parser.Tactic.SolveByElim.erase]
public def fmtSolveByElimErase : Fmt := fun
  | `(Parser.Tactic.SolveByElim.erase| -%$minusTk $e:term) => do
    let minusTk ← fmt minusTk
    let e ← fmt e
    return Layouts.prefixOperator minusTk e .withoutSpacingIfAtomic
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.SolveByElim.arg]
public def fmtSolveByElimArg : Fmt := fun
  | `(Parser.Tactic.SolveByElim.arg| $x:star) => fmt x
  | `(Parser.Tactic.SolveByElim.arg| $x:erase) => fmt x
  | `(Parser.Tactic.SolveByElim.arg| $x:term) => fmt x
  | _ => throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.solveByElim]
public def fmtSolveByElim : Fmt := fun
  | `(tactic| solve_by_elim%$tk $[*%$starTk?]? $cfg:optConfig $[only%$only?]?
      $[[%$lbTk? $args?:arg,* ]%$rbTk?]? $[using%$usingTk? $ids?:ident,*]?) => do
    let tk ← fmt tk
    let starTk? ← fmt? starTk?
    let lhs := Layouts.atomic #[tk, starTk?]
    let ids? ← fmtTSepArray <| ids?.getD ⟨#[]⟩
    fmtSimpaLike lhs cfg none only? lbTk? args? rbTk? usingTk? ids?
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.applyAssumption]
public def fmtApplyAssumption : Fmt := fun
  | `(tactic| apply_assumption%$tk $cfg:optConfig $[only%$only?]? $[[%$lbTk? $args?:arg,* ]%$rbTk?]? $[using%$usingTk? $ids?:ident,*]?) =>
    do
      let lhs ← fmt tk
      let ids? ← fmtTSepArray <| ids?.getD ⟨#[]⟩
      fmtSimpaLike lhs cfg none only? lbTk? args? rbTk? usingTk? ids?
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.applyRules]
public def fmtApplyRules : Fmt := fun
  | `(tactic| apply_rules%$tk $cfg:optConfig $[only%$only?]? $[[%$lbTk? $args?:arg,* ]%$rbTk?]? $[using%$usingTk? $ids?:ident,*]?) =>
    do
      let lhs ← fmt tk
      let ids? ← fmtTSepArray <| ids?.getD ⟨#[]⟩
      fmtSimpaLike lhs cfg none only? lbTk? args? rbTk? usingTk? ids?
  | _ =>
    throw .partialFormatter

end

@[builtin_fmt Lean.Parser.Tactic.clearValueHyp]
public def fmtClearValueHyp : Fmt := fun
  | `(Parser.Tactic.clearValueHyp| (%$lbTk $hyp:binderIdent :%$colonTk $a:term =%$eqTk $b:term )%$rbTk) =>
    do
      let lbTk ← fmt lbTk
      let hyp ← fmt hyp
      let colonTk ← fmt colonTk
      let a ← fmt a
      let eqTk ← fmt eqTk
      let b ← fmt b
      let rbTk ← fmt rbTk
      let type := Layouts.infixOperator #[a, eqTk, b]
      return Layouts.binder #[lbTk] #[hyp] #[] colonTk type empty empty #[rbTk]
        (kind := .local (respectPseudoAlignment := true))
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.clearValueArg]
public def fmtClearValueArg : Fmt := fun
  | `(Parser.Tactic.clearValueArg| $x:clearValueStar) => fmt x
  | `(Parser.Tactic.clearValueArg| $x:clearValueHyp) => fmt x
  | `(Parser.Tactic.clearValueArg| $x:term) => fmt x
  | _ => throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.rwRule]
public def fmtRwRule : Fmt := fun
  | `(Parser.Tactic.rwRule| $[←%$revTk?]? $e:term) => do
    let revTk? ← fmt? revTk?
    let e ← fmt e
    return Layouts.prefixOperator revTk? e .withSpacing
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.rwRuleSeq]
public def fmtRwRuleSeq : Fmt := fun
  | `(Parser.Tactic.rwRuleSeq| [%$lbTk $rules:rwRule,* ]%$rbTk) => do
    let lbTk ← fmt lbTk
    let rules ← fmtTSepArray rules
    let rbTk ← fmt rbTk
    return Layouts.collection lbTk rules rbTk
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.rewriteSeq]
public def fmtRewrite : Fmt := fun
  | `(tactic| rewrite%$rewriteTk $cfg:optConfig $rules:rwRuleSeq $[$loc?:location]?) => do
    fmtRwLike rewriteTk cfg rules loc?
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.rwSeq]
public def fmtRw : Fmt := fun
  | `(tactic| rw%$rwTk $cfg:optConfig $rules:rwRuleSeq $[$loc?:location]?) => do
    fmtRwLike rwTk cfg rules loc?
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.rwa]
public def fmtRwa : Fmt := fun
  | `(tactic| rwa%$rwaTk $rules:rwRuleSeq) => do
    let rwaTk ← fmt rwaTk
    let rules ← fmt rules
    return Layouts.pseudoApplication #[rwaTk, rules]
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.rwaAt]
public def fmtRwaAt : Fmt := fun
  | `(tactic| rwa%$rwaTk $rules:rwRuleSeq at%$atTk $t:term) => do
    let rwaTk ← fmt rwaTk
    let rules ← fmt rules
    let atTk ← fmt atTk
    let t ← fmt t
    let lhs := Layouts.pseudoApplication #[rwaTk, rules]
    let location := Layouts.pseudoApplication #[atTk, t]
    return Layouts.pseudoApplication #[lhs, location]
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.rwaAtLegacyLocation]
public def fmtRwaAtLegacyLocation : Fmt := fun
  | `(tactic| rwa%$rwaTk $rules:rwRuleSeq $loc:location) => do
    let rwaTk ← fmt rwaTk
    let rules ← fmt rules
    let lhs := Layouts.pseudoApplication #[rwaTk, rules]
    fmtWithLocationSuffix lhs loc
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.rewrites?]
public def fmtRewrites? : Fmt := fun
  | `(tactic| rw?%$rwTk $[$loc?:location]? $[$forbidden:rewrites_forbidden]?) => do
    let rwTk ← fmt rwTk
    let loc? ← fmt? loc?
    let forbidden ← fmt? forbidden
    return Layouts.blocks #[rwTk, loc?, forbidden]
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.rewrites_forbidden]
public def fmtRewritesForbidden : Fmt := fun stx => do
  let lbTk ← fmt (← getStxArg! stx 0)
  let argsAndSeps := (← getStxArg! stx 1).getArgs
  let rbTk ← fmt (← getStxArg! stx 2)
  let elemsAndSeps ←
    argsAndSeps.mapIdxM fun i elem => do
      if i % 2 == 0 then
        let minusTk ← fmt (← getStxArg! elem 0)
        let id ← fmt (← getStxArg! elem 1)
        return Layouts.prefixOperator minusTk id .withoutSpacing
      else
        fmt elem
  let elems : TaggedDoc.SepArray "," := ⟨elemsAndSeps⟩
  return Layouts.collection lbTk elems rbTk

@[builtin_fmt Lean.Parser.Tactic.injection]
public def fmtInjection : Fmt := fun
  | `(tactic| injection%$injectionTk $e:term $[with%$withTk? $ids?*]?) => do
    let injectionTk ← fmt injectionTk
    let e ← fmt e
    let lhs := Layouts.pseudoApplication #[injectionTk, e]
    let withTk? ← fmt? withTk?
    let ids ← fmtArray (ids?.getD #[])
    let ids := Layouts.fill ids
    let «with» := Layouts.keywordPrefixedTerm withTk? ids
    return Layouts.pseudoApplication #[lhs, «with»]
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.delta]
public def fmtDelta : Fmt := fun
  | `(tactic| delta%$deltaTk $ids:ident* $[$loc:location]?) => do
    let deltaTk ← fmt deltaTk
    let ids ← fmtArray ids
    let lhs := Layouts.pseudoApplication <| #[deltaTk] ++ ids
    fmtWithLocationSuffix lhs loc
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.unfold]
public def fmtUnfold : Fmt := fun
  | `(tactic| unfold%$unfoldTk $ids:ident* $[$loc:location]?) => do
    let unfoldTk ← fmt unfoldTk
    let ids ← fmtArray ids
    let lhs := Layouts.pseudoApplication <| #[unfoldTk] ++ ids
    fmtWithLocationSuffix lhs loc
  | _ =>
    throw .partialFormatter

public def fmtTacticLetDecl
    (kwTk : Syntax) (config? : Option (TSyntax ``Parser.Term.letConfig))
    (decl : TSyntax ``Parser.Term.letDecl)
    : FmtM TaggedDoc := do
  let kwTk ← fmt kwTk
  let config? ← fmt? config?
  let decl ← fmt decl
  return Layouts.letDecl kwTk config? decl

@[builtin_fmt Lean.Parser.Tactic.tacticHave__]
public def fmtTacticHave : Fmt := fun
  | `(tactic| have%$haveTk $cfg:letConfig $decl:letDecl) => fmtTacticLetDecl haveTk cfg decl
  | _ => throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.tacticLet__]
public def fmtTacticLet : Fmt := fun
  | `(tactic| let%$letTk $cfg:letConfig $decl:letDecl) => fmtTacticLetDecl letTk cfg decl
  | _ => throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.tacticHave']
public def fmtTacticHave' : Fmt := fun
  | `(tactic| have'%$haveTk $cfg:letConfig $decl:letDecl) => fmtTacticLetDecl haveTk cfg decl
  | _ => throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.tacticLet'__]
public def fmtTacticLet' : Fmt := fun
  | `(tactic| let'%$letTk $cfg:letConfig $decl:letDecl) => fmtTacticLetDecl letTk cfg decl
  | _ => throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.replace]
public def fmtReplace : Fmt := fun
  | `(tactic| replace%$replaceTk $decl:letDecl) => fmtTacticLetDecl replaceTk none decl
  | _ => throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.tacticHaveI__]
public def fmtTacticHaveI : Fmt := fun
  | `(tactic| haveI%$haveITk $cfg:letConfig $decl:letDecl) => fmtTacticLetDecl haveITk cfg decl
  | _ => throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.tacticLetI__]
public def fmtTacticLetI : Fmt := fun
  | `(tactic| letI%$letITk $cfg:letConfig $decl:letDecl) => fmtTacticLetDecl letITk cfg decl
  | _ => throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.tacticSuffices_]
public def fmtTacticSuffices : Fmt := fun
  | `(tactic| suffices%$sufficesTk $x:ident :%$colonTk $goal:term from%$fromTk $proof:term) =>
    fmtSufficesDecl sufficesTk x colonTk goal fromTk proof
  | `(tactic| suffices%$sufficesTk _%$x :%$colonTk $goal:term from%$fromTk $proof:term) =>
    fmtSufficesDecl sufficesTk x colonTk goal fromTk proof
  | `(tactic| suffices%$sufficesTk $_:hygieneInfo $goal:term from%$fromTk $proof:term) =>
    fmtSufficesDecl sufficesTk none none goal fromTk proof
  | `(tactic| suffices%$sufficesTk $x:ident :%$colonTk $goal:term by%$byTk $tac:tacticSeq) =>
    fmtSufficesDecl sufficesTk x colonTk goal byTk tac
  | `(tactic| suffices%$sufficesTk _%$x :%$colonTk $goal:term by%$byTk $tac:tacticSeq) =>
    fmtSufficesDecl sufficesTk x colonTk goal byTk tac
  | `(tactic| suffices%$sufficesTk $_:hygieneInfo $goal:term by%$byTk $tac:tacticSeq) =>
    fmtSufficesDecl sufficesTk none none goal byTk tac
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.letrec]
public def fmtTacticLetrec : Fmt := fun
  | `(tactic| let%$letTk rec%$recTk $decls:letRecDecls) => fmtFullLetRecDecl #[letTk, recTk] decls
  | _ => throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.generalizeArg]
public def fmtGeneralizeArg : Fmt := fun
  | `(Parser.Tactic.generalizeArg| $[$h?:ident :%$colonTk?]? $e:term =%$eqTk $x:ident) => do
    let h? ← fmt? h?
    let colonTk? ← fmt? colonTk?
    let e ← fmt e
    let eqTk ← fmt eqTk
    let x ← fmt x
    let inner := Layouts.infixOperator #[e, eqTk, x]
    return Layouts.typeAscription h? colonTk? inner
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.generalize]
public def fmtGeneralize : Fmt := fun
  | `(tactic| generalize%$generalizeTk $args:generalizeArg,* $[$loc:location]?) => do
    let generalizeTk ← fmt generalizeTk
    let args ← fmtTSepArray args
    let lhs := Layouts.keywordPrefixedSepFill generalizeTk args .nonSticky
    fmtWithLocationSuffix lhs loc
  | _ =>
    throw .partialFormatter

public def fmtCaseDeclaration
    (caseTk : Syntax) (args : Syntax.TSepArray ``Parser.Tactic.caseArg sep) (arrowTk : Syntax)
    (tac : Syntax)
    : FmtM TaggedDoc := do
  let caseTk ← fmt caseTk
  let args ← fmtTSepArray args
  let arrowTk ← fmt arrowTk
  let tac ← fmt tac
  let args := Layouts.horizontalOrVertical <| joinAltPats empty args
  let lhs := Layouts.prefixOperator caseTk args .withSpacing
  return Layouts.assignmentDeclaration lhs arrowTk tac

@[builtin_fmt Lean.Parser.Tactic.case]
public def fmtTacticCase : Fmt := fun
  | `(Parser.Tactic.case| case%$caseTk $args:caseArg|* =>%$arrowTk $tac:tacticSeq) =>
    fmtCaseDeclaration caseTk args arrowTk tac
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.case']
public def fmtTacticCase' : Fmt := fun
  | `(Parser.Tactic.case'| case'%$caseTk $args:caseArg|* =>%$arrowTk $tac:tacticSeq) =>
    fmtCaseDeclaration caseTk args arrowTk tac
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.elimTarget]
public def fmtElimTarget : Fmt := fun
  | `(Parser.Tactic.elimTarget| $[$hIdent?:binderIdent :%$colonTk?]? $term:term) => do
    let hIdent? ← fmt? hIdent?
    let colonTk? ← fmt? colonTk?
    let term ← fmt term
    return Layouts.typeAscription hIdent? colonTk? term
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.inductionAltLHS]
public def fmtInductionAltLHS : Fmt := fun
  | `(Parser.Tactic.inductionAltLHS| |%$pipeTk $[@%$atTk?]? $ctor:ident $discrims*) => do
    let pipeTk ← fmt pipeTk
    let atTk? ← fmt? atTk?
    let ctor ← fmt ctor
    let ctor := Layouts.prefixOperator atTk? ctor .withoutSpacing
    let discrims ← fmtArray discrims
    let operand := Layouts.pseudoApplication <| #[ctor] ++ discrims
    return nested <| Layouts.spacedAtomic #[pipeTk, operand]
  | `(Parser.Tactic.inductionAltLHS| |%$pipeTk $ctor:hole $discrims*) => do
    let pipeTk ← fmt pipeTk
    let ctor ← fmt ctor
    let discrims ← fmtArray discrims
    let operand := Layouts.pseudoApplication <| #[ctor] ++ discrims
    return nested <| Layouts.spacedAtomic #[pipeTk, operand]
  | _ =>
    throw .partialFormatter

public def fmtInductionAlt : Syntax → FmtM Layouts.Types.Alt := fun
  | `(Parser.Tactic.inductionAlt| $lhses:inductionAltLHS* $[=>%$arrowTk? $rhs?]?) => do
    if lhses.isEmpty then
      throw .partialFormatter
    let mut lhses ← fmtArray lhses
    let arrowTk? ← fmt? arrowTk?
    let rhs? ← fmt? rhs?
    return Layouts.alt lhses arrowTk? rhs?
  | _ =>
    throw .partialFormatter

public def fmtWithInductionAlts
    (lhs : TaggedDoc) (inductionAlts : TSyntax ``Parser.Tactic.inductionAlts)
    : FmtM TaggedDoc := do
  match inductionAlts with
  | `(Parser.Tactic.inductionAlts| with%$withTk $[$withTac?:tactic]? $alts:inductionAlt*) => do
    let withTk ← fmt withTk
    let withTac? ← fmt? withTac?
    let keyword := Layouts.pseudoApplication #[withTk, withTac?]
    let alts ← alts.mapM fmtInductionAlt
    let alts := Layouts.alts alts
    return Layouts.keywordSeparated lhs keyword alts {
      allowFlattening := false
      nestedRhs := false
    }
  | _ =>
    throw .partialFormatter

public def fmtInductionLike
    (keywordTk : Syntax) (discriminants : SepArray ",") (usingTk? : Option Syntax)
    (usingTerm? : Option Term) (generalizingTk? : Option Syntax) (generalizingTerms : Array Term)
    (inductionAlts? : Option (TSyntax ``Parser.Tactic.inductionAlts))
    : FmtM TaggedDoc := do
  let keywordTk ← fmt keywordTk
  let usingTk? ← fmt? usingTk?
  let usingTerm? ← fmt? usingTerm?
  let generalizingTk? ← fmt? generalizingTk?
  let generalizingTerms ← fmtArray generalizingTerms
  let head := Layouts.keywordPrefixedSepFill keywordTk discriminants .nonSticky
  let usingClause := Layouts.keywordPrefixedTerm usingTk? usingTerm?
  let generalizingTerms := Layouts.fill generalizingTerms
  let generalizingClause := Layouts.keywordPrefixedTerm generalizingTk? generalizingTerms
  let lhs := Layouts.blocks #[head, usingClause, generalizingClause]
  match inductionAlts? with
  | some inductionAlts => fmtWithInductionAlts lhs inductionAlts
  | none => return lhs

@[builtin_fmt Lean.Parser.Tactic.induction]
public def fmtTacticInduction : Fmt := fun
  | `(Parser.Tactic.induction|
      induction%$inductionTk $targets:elimTarget,*
        $[using%$usingTk? $usingTerm?:term]?
        $[generalizing%$generalizingTk? $generalizingTerms?:term*]?
        $[$alts?:inductionAlts]?) => do
    let targets ← fmtTSepArray targets
    fmtInductionLike inductionTk targets usingTk? usingTerm? generalizingTk?
      (generalizingTerms?.getD #[]) alts?
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.cases]
public def fmtTacticCases : Fmt := fun
  | `(Parser.Tactic.cases|
      cases%$casesTk $targets:elimTarget,*
        $[using%$usingTk? $usingTerm?:term]?
        $[$alts?:inductionAlts]?) => do
    let targets ← fmtTSepArray targets
    fmtInductionLike casesTk targets usingTk? usingTerm? none #[] alts?
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.funInduction]
public def fmtFunInduction : Fmt := fun
  | `(Parser.Tactic.funInduction|
      fun_induction%$funInductionTk $f:term
        $[generalizing%$generalizingTk? $generalizingTerms?:term*]?
        $[$alts?:inductionAlts]?) => do
    let f ← fmt f
    fmtInductionLike funInductionTk ⟨#[f]⟩ none none generalizingTk? (generalizingTerms?.getD #[])
      alts?
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.funCases]
public def fmtFunCases : Fmt := fun
  | `(Parser.Tactic.funCases| fun_cases%$funCasesTk $f:term $[$alts?:inductionAlts]?) => do
    let f ← fmt f
    fmtInductionLike funCasesTk ⟨#[f]⟩ none none none #[] alts?
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.change]
public def fmtChange : Fmt := fun
  | `(tactic| change%$changeTk $t:term $[$loc:location]?) => do
    let changeTk ← fmt changeTk
    let t ← fmt t
    let lhs := Layouts.pseudoApplication #[changeTk, t]
    fmtWithLocationSuffix lhs loc
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.«show»]
public def fmtTacticShow : Fmt := fun
  | `(tactic| show%$showTk $t:term) => do
    let showTk ← fmt showTk
    let t ← fmt t
    return Layouts.pseudoApplication #[showTk, t]
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.split]
public def fmtSplit : Fmt := fun
  | `(tactic| split%$splitTk $[$e:term]? $[$loc:location]?) => do
    let splitTk ← fmt splitTk
    let e ← fmt? e
    let lhs := Layouts.pseudoApplication #[splitTk, e]
    fmtWithLocationSuffix lhs loc
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.letToHave]
public def fmtLetToHave : Fmt := fun
  | `(tactic| let_to_have%$letToHaveTk $[$loc:location]?) => do
    let letToHaveTk ← fmt letToHaveTk
    fmtWithLocationSuffix letToHaveTk loc
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.«tacticExists_,,»]
public def fmtTacticExists : Fmt := fun
  | `(tactic| exists%$existsTk $es:term,*) => do
    let existsTk ← fmt existsTk
    let es ← fmtTSepArray es
    return Layouts.keywordPrefixedSepFill existsTk es .nonSticky
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.«tacticNomatch_,,»]
public def fmtTacticNomatch : Fmt := fun
  | `(tactic| nomatch%$nomatchTk $es:term,*) => do
    let nomatchTk ← fmt nomatchTk
    let es ← fmtTSepArray es
    return Layouts.keywordPrefixedSepFill nomatchTk es .nonSticky
  | _ =>
    throw .partialFormatter

@[builtin_conditional_fmt Lean.Parser.Tactic.tacIfThenElse]
public def fmtTacIfThenElse : ConditionalFmt := fun
  | `(tactic| if%$ifTk $c:term then%$thenTk $thenBody:tacticSeq else%$elseTk $elseBody:tacticSeq) =>
    do
      let cond ← fmt c
      return some { ifTk, cond, thenTk, thenBody, elseTk? := elseTk, elseBody? := elseBody }
  | _ =>
    pure none

@[builtin_conditional_fmt Lean.Parser.Tactic.tacDepIfThenElse]
public def fmtTacDepIfThenElse : ConditionalFmt := fun
  | `(tactic| if%$ifTk $h:binderIdent :%$colonTk $c:term then%$thenTk $thenBody else%$elseTk $elseBody) =>
    do
      let h ← fmt h
      let colonTk ← fmt colonTk
      let c ← fmt c
      let cond := Layouts.typeAscription h colonTk c
      return some { ifTk, cond, thenTk, thenBody, elseTk? := elseTk, elseBody? := elseBody }
  | _ =>
    pure none

@[builtin_fmt Lean.Parser.Tactic.decide]
public def fmtDecide : Fmt := fun
  | `(tactic| decide%$decideTk $cfg:optConfig) => do
    let decideTk ← fmt decideTk
    let cfg ← (← tacticOptConfigItems cfg).mapM fmt
    return Layouts.pseudoApplication <| #[decideTk] ++ cfg
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.nativeDecide]
public def fmtNativeDecide : Fmt := fun
  | `(tactic| native_decide%$nativeDecideTk $cfg:optConfig) => do
    let nativeDecideTk ← fmt nativeDecideTk
    let cfg ← (← tacticOptConfigItems cfg).mapM fmt
    return Layouts.pseudoApplication <| #[nativeDecideTk] ++ cfg
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.omega]
public def fmtOmega : Fmt := fun
  | `(tactic| omega%$omegaTk $cfg:optConfig) => do
    let omegaTk ← fmt omegaTk
    let cfg ← (← tacticOptConfigItems cfg).mapM fmt
    return Layouts.pseudoApplication <| #[omegaTk] ++ cfg
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.tacticAssumption_mod_cast_]
public def fmtAssumptionModCast : Fmt := fun
  | `(tactic| assumption_mod_cast%$assumptionTk $cfg:optConfig) => do
    let assumptionTk ← fmt assumptionTk
    let cfg ← (← tacticOptConfigItems cfg).mapM fmt
    return Layouts.pseudoApplication <| #[assumptionTk] ++ cfg
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.bvTypes]
public def fmtBvTypes : Fmt := fun
  | `(Parser.Tactic.bvTypes| types%$typesTk [%$lbTk $types:ident,* ]%$rbTk) => do
    let typesTk ← fmt typesTk
    let lbTk ← fmt lbTk
    let types ← fmtTSepArray types
    let rbTk ← fmt rbTk
    return Layouts.keywordPrefixedCollection typesTk lbTk types rbTk
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.bvCheck]
public def fmtBvCheck : Fmt := fun
  | `(tactic| bv_check%$bvCheckTk $cfg:optConfig $[$types?:bvTypes]? $lratFile:str) => do
    let bvCheckTk ← fmt bvCheckTk
    let cfg ← (← tacticOptConfigItems cfg).mapM fmt
    let types? ← fmt? types?
    let lratFile ← fmt lratFile
    let lhs := Layouts.pseudoApplication <| #[bvCheckTk] ++ cfg
    return Layouts.blocks #[lhs, types?, lratFile]
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.bvDecide]
public def fmtBvDecide : Fmt := fun
  | `(tactic| bv_decide%$bvDecideTk $cfg:optConfig $[$types?:bvTypes]?) => do
    let bvDecideTk ← fmt bvDecideTk
    let cfg ← (← tacticOptConfigItems cfg).mapM fmt
    let types? ← fmt? types?
    let lhs := Layouts.pseudoApplication <| #[bvDecideTk] ++ cfg
    return Layouts.blocks #[lhs, types?]
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.bvTrace]
public def fmtBvTrace : Fmt := fun
  | `(tactic| bv_decide?%$bvDecideTk $cfg:optConfig $[$types?:bvTypes]?) => do
    let bvDecideTk ← fmt bvDecideTk
    let cfg ← (← tacticOptConfigItems cfg).mapM fmt
    let types? ← fmt? types?
    let lhs := Layouts.pseudoApplication <| #[bvDecideTk] ++ cfg
    return Layouts.blocks #[lhs, types?]
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.bvNormalize]
public def fmtBvNormalize : Fmt := fun
  | `(tactic| bv_normalize%$bvNormalizeTk $cfg:optConfig $[$types?:bvTypes]?) => do
    let bvNormalizeTk ← fmt bvNormalizeTk
    let cfg ← (← tacticOptConfigItems cfg).mapM fmt
    let types? ← fmt? types?
    let lhs := Layouts.pseudoApplication <| #[bvNormalizeTk] ++ cfg
    return Layouts.blocks #[lhs, types?]
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.normCast0]
public def fmtNormCast0 : Fmt := fun
  | `(tactic| norm_cast0%$normCastTk $cfg:optConfig $[$loc:location]?) => do
    let normCastTk ← fmt normCastTk
    let cfg ← (← tacticOptConfigItems cfg).mapM fmt
    let lhs := Layouts.pseudoApplication <| #[normCastTk] ++ cfg
    fmtWithLocationSuffix lhs loc
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.tacticNorm_cast__]
public def fmtNormCast : Fmt := fun
  | `(tactic| norm_cast%$normCastTk $cfg:optConfig $[$loc:location]?) => do
    let normCastTk ← fmt normCastTk
    let cfg ← (← tacticOptConfigItems cfg).mapM fmt
    let lhs := Layouts.pseudoApplication <| #[normCastTk] ++ cfg
    fmtWithLocationSuffix lhs loc
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.acNf0]
public def fmtAcNf0 : Fmt := fun
  | `(tactic| ac_nf0%$acNfTk $[$loc:location]?) => do
    let acNfTk ← fmt acNfTk
    fmtWithLocationSuffix acNfTk loc
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.tacticAc_nf_]
public def fmtAcNf : Fmt := fun
  | `(tactic| ac_nf%$acNfTk $[$loc:location]?) => do
    let acNfTk ← fmt acNfTk
    fmtWithLocationSuffix acNfTk loc
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.symm]
public def fmtSymm : Fmt := fun
  | `(tactic| symm%$symmTk $[$loc:location]?) => do
    let symmTk ← fmt symmTk
    fmtWithLocationSuffix symmTk loc
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.cbv]
public def fmtCbv : Fmt := fun
  | `(tactic| cbv%$cbvTk $[$loc:location]?) => do
    let cbvTk ← fmt cbvTk
    fmtWithLocationSuffix cbvTk loc
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.impossible]
public def fmtImpossible : Fmt := fun
  | `(tactic| impossible%$impossibleTk $cfg:optConfig by%$byTk $tac:tacticSeq) => do
    let impossibleTk ← fmt impossibleTk
    let cfg ← (← tacticOptConfigItems cfg).mapM fmt
    let lhs := Layouts.pseudoApplication <| #[impossibleTk] ++ cfg
    let byTk ← fmt byTk
    let tac ← fmt tac
    return Layouts.keywordSeparated lhs byTk tac
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.exact?]
public def fmtExact? : Fmt := fun stx => do
  let `(tactic| exact? $cfg:optConfig $[using%$usingTk? $ids?:ident,*]?) := stx
    | throw .partialFormatter
  let exactTk ← getStxArg! stx 0
  let exactTk ← fmt exactTk
  let cfg ← (← tacticOptConfigItems cfg).mapM fmt
  let lhs := Layouts.pseudoApplication <| #[exactTk] ++ cfg
  let usingTk? ← fmt? usingTk?
  let ids ← fmtTSepArray (ids?.getD ⟨#[]⟩)
  let «using» := Layouts.keywordPrefixedSepFill usingTk? ids .sticky
  return Layouts.pseudoApplication #[lhs, «using»]

@[builtin_fmt Lean.Parser.Tactic.apply?]
public def fmtApply? : Fmt := fun
  | `(tactic| apply?%$applyTk $cfg:optConfig $[using%$usingTk? $ids?:term,*]?) => do
    let applyTk ← fmt applyTk
    let cfg ← (← tacticOptConfigItems cfg).mapM fmt
    let lhs := Layouts.pseudoApplication <| #[applyTk] ++ cfg
    let usingTk? ← fmt? usingTk?
    let ids ← fmtTSepArray (ids?.getD ⟨#[]⟩)
    let «using» := Layouts.keywordPrefixedSepFill usingTk? ids .sticky
    return Layouts.pseudoApplication #[lhs, «using»]
  | _ =>
    throw .partialFormatter

public def fmtExtractLetsLike
    (extractLetsTk : Syntax) (cfg : TSyntax ``Parser.Tactic.optConfig) (args : Array (TSyntax k))
    (loc? : Option (TSyntax `Lean.Parser.Tactic.location))
    : FmtM TaggedDoc := do
  let extractLetsTk ← fmt extractLetsTk
  let cfgItems ← (← tacticOptConfigItems cfg).mapM fmt
  let args ← fmtArray args
  let extractLets := Layouts.pseudoApplication <| #[extractLetsTk] ++ cfgItems ++ args
  fmtWithLocationSuffix extractLets loc?

@[builtin_fmt Lean.Parser.Tactic.extractLets]
public def fmtExtractLets : Fmt := fun
  | `(tactic| extract_lets%$extractLetsTk $cfg:optConfig $args* $[$loc?:location]?) => do
    fmtExtractLetsLike extractLetsTk cfg args loc?
  | _ =>
    throw .partialFormatter

public def fmtLiftLetsLike (liftLetsTk : Syntax) (cfg : TSyntax ``Parser.Tactic.optConfig)
    : FmtM TaggedDoc := do
  let liftLetsTk ← fmt liftLetsTk
  let cfg ← (← tacticOptConfigItems cfg).mapM fmt
  return Layouts.pseudoApplication <| #[liftLetsTk] ++ cfg

@[builtin_fmt Lean.Parser.Tactic.liftLets]
public def fmtLiftLets : Fmt := fun
  | `(tactic| lift_lets%$liftLetsTk $cfg:optConfig $[$loc:location]?) => do
    fmtWithLocationSuffix (← fmtLiftLetsLike liftLetsTk cfg) loc
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.by?]
public def fmtBy? : Fmt := fun
  | `(by?%$byTk $tac:tacticSeq) => do
    let byTk ← fmt byTk
    let tac ← fmt tac
    return Layouts.keywordPrefixedSeq byTk tac .sticky
  | _ =>
    throw .partialFormatter

@[builtin_fmt «term‹_›»]
public def fmtAnonymousHyp : Fmt := fun
  | `(‹%$lbTk $t:term ›%$rbTk) => do
    let lbTk ← fmt lbTk
    let t ← fmt t
    let rbTk ← fmt rbTk
    return Layouts.bracketed lbTk t rbTk .dense
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Attr.cbv_eval]
public def fmtCbvEval : Fmt := fun
  | `(Parser.Attr.cbv_eval| cbv_eval%$cbvEvalTk $[←%$revTk?]? $[$id?:ident]?) => do
    let cbvEvalTk ← fmt cbvEvalTk
    let revTk? ← fmt? revTk?
    let id? ← fmt? id?
    let rhs := Layouts.prefixOperator revTk? id? .withSpacing
    return Layouts.pseudoApplication #[cbvEvalTk, rhs]
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Attr.norm_cast]
public def fmtNormCastAttr : Fmt := fun
  | `(Parser.Attr.norm_cast| norm_cast%$normCastTk $[$label?:normCastLabel]? $[$prio?:num]?) => do
    let normCastTk ← fmt normCastTk
    let label? ← fmt? label?
    let prio? ← fmt? prio?
    return Layouts.pseudoApplication #[normCastTk, label?, prio?]
  | _ =>
    throw .partialFormatter
