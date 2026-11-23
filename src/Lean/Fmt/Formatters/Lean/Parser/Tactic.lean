/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Marc Huisinga
-/
module

prelude
public import Lean.Fmt.FmtM.Basic
public import Lean.Fmt.Formatters.Lean.Parser.Term.Basic
meta import Lean.Parser.Tactic
import Lean.Fmt.FmtM.CommonFormatters
import Init.Data

namespace Lean.Fmt

@[builtin_fmt Lean.Parser.Tactic.unknown]
public def fmtUnknownTactic : Fmt := fun stx => do fmt (← getStxArg! stx 0)

@[builtin_fmt Lean.Parser.Tactic.match]
public def fmtTacticMatch : Fmt := fun
  | `(Parser.Tactic.match|
      match%$matchTk $[$generalizingParam?:generalizingParam]? $[$motive?:motive]? $matchDiscrs:matchDiscr,* with%$withTk
      $matchAlts:matchAlts) => do
    let matchTk ← fmt matchTk
    let generalizingParam? ← fmt? generalizingParam?
    let motive? ← fmt? motive?
    let matchLhs := Layouts.pseudoApplication #[matchTk, generalizingParam?, motive?]
    let matchDiscrs ← fmtTSepArray matchDiscrs
    let withTk ← fmt withTk
    let matchAlts ← fmt matchAlts
    let «match» := Layouts.keywordPrefixedSepFill matchLhs matchDiscrs .nonSticky
    return Layouts.keywordSeparated «match» withTk matchAlts {
      allowFlattening := false
      nestedRhs := false
    }
  | _ => throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.introMatch]
public def fmtIntroMatch : Fmt := fun
  | `(Parser.Tactic.introMatch| intro%$introTk $matchAlts:matchAlts) => do
    let introTk ← fmt introTk
    let matchAlts ← fmt matchAlts
    return Layouts.lines #[introTk, matchAlts]
  | _ => throw .partialFormatter
