/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Marc Huisinga
-/
module

prelude
public import Lean.Fmt.FmtM.Basic
meta import Init.Meta
import Lean.Fmt.FmtM.CommonFormatters
import Init.Data

namespace Lean.Fmt

@[builtin_fmt Lean.termEval_prec_]
public def fmtEvalPrec : Fmt := fun
  | `(eval_prec%$evalPrecTk $p:prec) => do fmtAppLike #[evalPrecTk, p]
  | _ => throw .partialFormatter

@[builtin_fmt Lean.termEval_prio_]
public def fmtEvalPrio : Fmt := fun
  | `(eval_prio%$evalPrioTk $p:prio) => do fmtAppLike #[evalPrioTk, p]
  | _ => throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.tacticErw___]
public def fmtErw : Fmt := fun
  | `(tactic| erw%$erwTk $cfg:optConfig $rules:rwRuleSeq $[$loc?:location]?) => do
    fmtRwLike erwTk cfg rules loc?
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.simpAllKind]
public def fmtSimpAllKind : Fmt := fun
  | `(Parser.Tactic.simpAllKind| (%$lbTk all%$allTk :=%$colonEqTk true%$trueTk )%$rbTk) =>
    fmtNamedArgumentTerm lbTk allTk colonEqTk trueTk rbTk
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.dsimpKind]
public def fmtDsimpKind : Fmt := fun
  | `(Parser.Tactic.dsimpKind| (%$lbTk dsimp%$dsimpTk :=%$colonEqTk true%$trueTk )%$rbTk) =>
    fmtNamedArgumentTerm lbTk dsimpTk colonEqTk trueTk rbTk
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.declareSimpLikeTactic]
public def fmtDeclareSimpLikeTactic : Fmt := fun
  | `(Parser.Tactic.declareSimpLikeTactic|
      $[$doc?:docComment]? declare_simp_like_tactic%$declTk $[$opt?]?
        $tacName:ident $tacToken:str $cfg:optConfig) => do
    let doc? ← fmt? doc?
    let declTk ← fmt declTk
    let opt? ← fmt? opt?
    let declLhs := Layouts.pseudoApplication #[declTk, opt?]
    let tacName ← fmt tacName
    let tacToken ← fmt tacToken
    let cfgItems ← (← tacticOptConfigItems cfg).mapM fmt
    let decl := Layouts.pseudoApplication <| #[declLhs, tacName, tacToken] ++ cfgItems
    return Layouts.lines #[doc?, decl]
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.simpAutoUnfold]
public def fmtSimpAutoUnfold : Fmt := fun
  | `(tactic| simp!%$tk $cfg:optConfig $[$disch:discharger]? $[only%$only?]?
      $[[%$lbTk? $args?,* ]%$rbTk?]? $[$loc?:location]?) => do
    fmtSimpLike #[tk] cfg disch only? lbTk? args? rbTk? loc?
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.simpArith]
public def fmtSimpArith : Fmt := fun
  | `(tactic| simp_arith%$tk $cfg:optConfig $[$disch:discharger]? $[only%$only?]?
      $[[%$lbTk? $args?,* ]%$rbTk?]? $[$loc?:location]?) => do
    fmtSimpLike #[tk] cfg disch only? lbTk? args? rbTk? loc?
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.simpArithBang]
public def fmtSimpArithBang : Fmt := fun
  | `(tactic| simp_arith!%$tk $cfg:optConfig $[$disch:discharger]? $[only%$only?]?
      $[[%$lbTk? $args?,* ]%$rbTk?]? $[$loc?:location]?) => do
    fmtSimpLike #[tk] cfg disch only? lbTk? args? rbTk? loc?
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.simpAllAutoUnfold]
public def fmtSimpAllAutoUnfold : Fmt := fun
  | `(tactic| simp_all!%$tk $cfg:optConfig $[$disch:discharger]? $[only%$only?]?
      $[[%$lbTk? $args?,* ]%$rbTk?]?) =>
    fmtSimpLike #[tk] cfg disch only? lbTk? args? rbTk? none
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.simpAllArith]
public def fmtSimpAllArith : Fmt := fun
  | `(tactic| simp_all_arith%$tk $cfg:optConfig $[$disch:discharger]? $[only%$only?]?
      $[[%$lbTk? $args?,* ]%$rbTk?]?) =>
    fmtSimpLike #[tk] cfg disch only? lbTk? args? rbTk? none
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.simpAllArithBang]
public def fmtSimpAllArithBang : Fmt := fun
  | `(tactic| simp_all_arith!%$tk $cfg:optConfig $[$disch:discharger]? $[only%$only?]?
      $[[%$lbTk? $args?,* ]%$rbTk?]?) =>
    fmtSimpLike #[tk] cfg disch only? lbTk? args? rbTk? none
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.dsimpAutoUnfold]
public def fmtDSimpAutoUnfold : Fmt := fun
  | `(tactic| dsimp!%$tk $cfg:optConfig $[$disch:discharger]? $[only%$only?]?
      $[[%$lbTk? $args?,* ]%$rbTk?]? $[$loc?:location]?) => do
    fmtSimpLike #[tk] cfg disch only? lbTk? args? rbTk? loc?
  | _ =>
    throw .partialFormatter
