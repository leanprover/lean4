/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Marc Huisinga
-/
module

prelude
public import Lean.Fmt.FmtM.Basic
meta import Init.Try
import Lean.Fmt.FmtM.CommonFormatters
import Init.Data

namespace Lean.Fmt

@[builtin_fmt Lean.Parser.Tactic.tryTrace]
public def fmtTryTrace : Fmt := fun
  | `(tactic| try?%$tryTk $cfg:optConfig) => do
    let tryTk ← fmt tryTk
    let cfg ← (← tacticOptConfigItems cfg).mapM fmt
    return Layouts.pseudoApplication <| #[tryTk] ++ cfg
  | _ => throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.tryTraceWith]
public def fmtTryTraceWith : Fmt := fun
  | `(tactic| try?%$tryTk $cfg:optConfig =>%$arrowTk $seq:tacticSeq) => do
    let tryTk ← fmt tryTk
    let cfg ← (← tacticOptConfigItems cfg).mapM fmt
    let arrowTk ← fmt arrowTk
    let seq ← fmt seq
    let signature := Layouts.pseudoApplication <| #[tryTk] ++ cfg
    return Layouts.assignmentDeclaration signature arrowTk seq
  | _ => throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.attemptAll]
public def fmtAttemptAll : Fmt := fun
  | `(tactic| attempt_all%$attemptAllTk $[|%$barTks $tacticSeqs:tacticSeq]*) =>
    fmtAltsTactic attemptAllTk barTks tacticSeqs
  | _ => throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.attemptAllPar]
public def fmtAttemptAllPar : Fmt := fun
  | `(tactic| attempt_all_par%$attemptAllParTk $[|%$barTks $tacticSeqs:tacticSeq]*) =>
    fmtAltsTactic attemptAllParTk barTks tacticSeqs
  | _ => throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.firstPar]
public def fmtFirstPar : Fmt := fun
  | `(tactic| first_par%$firstParTk $[|%$barTks $tacticSeqs:tacticSeq]*) =>
    fmtAltsTactic firstParTk barTks tacticSeqs
  | _ => throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.tryResult]
public def fmtTryResult : Fmt := fun
  | `(tactic| try_suggestions%$trySuggestionsTk $tactics:tactic*) => do
    let trySuggestionsTk ← fmt trySuggestionsTk
    let tactics ← fmtArray tactics
    return Layouts.pseudoApplication <| #[trySuggestionsTk] ++ tactics
  | _ => throw .partialFormatter

@[builtin_fmt Lean.Parser.Command.registerTryTactic]
public def fmtRegisterTryTactic : Fmt := fun
  | `(command|
      $[$docComment?:docComment]?
      register_try?_tactic%$registerTk
        $[(%$lbTk? priority%$priorityTk? :=%$colonEqTk? $priority?:num )%$rbTk?]?
        $seq:tacticSeq) => do
    let registerTk ← fmt registerTk
    let priorityParam? ← fmtNamedArgumentTerm? lbTk? priorityTk? colonEqTk? priority? rbTk?
    let seq ← fmt seq
    let keyword := Layouts.pseudoApplication #[registerTk, priorityParam?]
    let decl := Layouts.keywordPrefixedSeq keyword seq .nonSticky
    fmtDeclWithModifiers docComment? none #[] decl
  | _ => throw .partialFormatter
