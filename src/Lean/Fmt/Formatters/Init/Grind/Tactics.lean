/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Marc Huisinga
-/
module

prelude
public import Lean.Fmt.FmtM.Basic
meta import Init.Grind.Tactics
import Lean.Fmt.FmtM.CommonFormatters
import Init.Data

namespace Lean.Fmt

@[builtin_fmt Lean.Parser.Tactic.grind]
public def fmtGrindTactic : Fmt := fun
  | `(tactic| grind%$grindTk $cfg:optConfig $[only%$only?]?
      $[[%$lbTk? $args?:grindParam,* ]%$rbTk?]? $[=>%$arrowTk? $seq?:grindSeq]?) => do
    let body ← fmtSimpLike #[grindTk] cfg none only? lbTk? args? rbTk? none
    let arrowTk? ← fmt? arrowTk?
    let seq? ← fmt? seq?
    return Layouts.assignmentDeclaration body arrowTk? seq?
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.grindTrace]
public def fmtGrindTraceTactic : Fmt := fun
  | `(tactic| grind?%$grindTk $cfg:optConfig $[only%$only?]?
      $[[%$lbTk? $args?:grindParam,* ]%$rbTk?]?) =>
    fmtSimpLike #[grindTk] cfg none only? lbTk? args? rbTk? none
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.sym]
public def fmtSymTactic : Fmt := fun
  | `(tactic| sym%$symTk $cfg:optConfig $[only%$only?]?
      $[[%$lbTk? $args?:grindParam,* ]%$rbTk?]? =>%$arrowTk $seq:grindSeq) => do
    let body ← fmtSimpLike #[symTk] cfg none only? lbTk? args? rbTk? none
    let arrowTk ← fmt arrowTk
    let seq ← fmt seq
    return Layouts.assignmentDeclaration body arrowTk seq
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.cutsat]
public def fmtCutsat : Fmt := fun
  | `(tactic| cutsat%$tk $cfg:optConfig) => do
    let tk ← fmt tk
    let cfg ← (← tacticOptConfigItems cfg).mapM fmt
    return Layouts.pseudoApplication <| #[tk] ++ cfg
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.lia]
public def fmtLiaTactic : Fmt := fun
  | `(tactic| lia%$tk $cfg:optConfig $[[%$lbTk? $args?:grindParam,* ]%$rbTk?]?) => do
    fmtSimpLike #[tk] cfg none none lbTk? args? rbTk? none
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.grind_order]
public def fmtGrindOrder : Fmt := fun
  | `(tactic| grind_order%$tk $cfg:optConfig) => do
    let tk ← fmt tk
    let cfg ← (← tacticOptConfigItems cfg).mapM fmt
    return Layouts.pseudoApplication <| #[tk] ++ cfg
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.grind_linarith]
public def fmtGrindLinarithTactic : Fmt := fun
  | `(tactic| grind_linarith%$tk $cfg:optConfig) => do
    let tk ← fmt tk
    let cfg ← (← tacticOptConfigItems cfg).mapM fmt
    return Layouts.pseudoApplication <| #[tk] ++ cfg
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.grobner]
public def fmtGrobner : Fmt := fun
  | `(tactic| grobner%$tk $cfg:optConfig $[[%$lbTk? $args?:grindParam,* ]%$rbTk?]?) => do
    fmtSimpLike #[tk] cfg none none lbTk? args? rbTk? none
  | _ =>
    throw .partialFormatter
