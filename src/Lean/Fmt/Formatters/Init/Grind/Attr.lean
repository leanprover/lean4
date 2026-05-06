/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Marc Huisinga
-/
module

prelude
public import Lean.Fmt.FmtM.Basic
meta import Init.Grind.Attr
import Lean.Fmt.FmtM.CommonFormatters
import Init.Data

namespace Lean.Fmt

@[builtin_fmt Lean.Parser.Attr.grindEq]
public def fmtGrindEq : Fmt := fun
  | `(Parser.Attr.grindEq| =%$eqTk $[$gen?:grindGen]?) => do
    let eqTk ← fmt eqTk
    let gen? ← fmt? gen?
    return Layouts.prefixOperator eqTk gen? .withSpacing
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Attr.grindEqRhs]
public def fmtGrindEqRhs : Fmt := fun
  | `(Parser.Attr.grindEqRhs| =%$eqTk _%$underTk $[$gen?:grindGen]?) => do
    let eqTk ← fmt eqTk
    let underTk ← fmt underTk
    let gen? ← fmt? gen?
    let op := Layouts.atomic #[eqTk, underTk]
    return Layouts.prefixOperator op gen? .withSpacing
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Attr.grindEqBoth]
public def fmtGrindEqBoth : Fmt := fun
  | `(Parser.Attr.grindEqBoth| _%$u1 =%$eqTk _%$u2 $[$gen?:grindGen]?) => do
    let u1 ← fmt u1
    let eqTk ← fmt eqTk
    let u2 ← fmt u2
    let gen? ← fmt? gen?
    let op := Layouts.atomic #[u1, eqTk, u2]
    return Layouts.prefixOperator op gen? .withSpacing
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Attr.grindEqBwd]
public def fmtGrindEqBwd : Fmt := fun stx => do
  let grp ← getStxArg! (← getStxArg! stx 0) 0
  let arrowTk ← fmt (← getStxArg! grp 0)
  let eqTk ← fmt (← getStxArg! grp 1)
  return Layouts.atomic #[arrowTk, eqTk]

@[builtin_fmt Lean.Parser.Attr.grindBwd]
public def fmtGrindBwd : Fmt := fun stx => do
  let arrowTk ← fmtAtomic (← getStxArg! stx 0)
  let gen? ← fmt? (← getStxArg! stx 1).getArgs[0]?
  return Layouts.prefixOperator arrowTk gen? .withSpacing

@[builtin_fmt Lean.Parser.Attr.grindDef]
public def fmtGrindDef : Fmt := fun stx => do
  let defTk ← fmtAtomic (← getStxArg! stx 0)
  let gen? ← fmt? (← getStxArg! stx 1).getArgs[0]?
  return Layouts.prefixOperator defTk gen? .withSpacing

@[builtin_fmt Lean.Parser.Attr.grindCasesEager]
public def fmtGrindCasesEager : Fmt := fun
  | `(Parser.Attr.grindCasesEager| cases%$casesTk eager%$eagerTk) => do
    let casesTk ← fmt casesTk
    let eagerTk ← fmt eagerTk
    return Layouts.spacedAtomic #[casesTk, eagerTk]
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Attr.grindNorm]
public def fmtGrindNorm : Fmt := fun stx => do
  let normTk ← fmt (← getStxArg! stx 0)
  let prePost? ← fmt? (← getStxArg! stx 1).getArgs[0]?
  let arrow? ←
    match (← getStxArg! stx 2).getArgs[0]? with
    | some arrow => fmtAtomic arrow
    | none => pure empty
  return Layouts.spacedAtomic #[normTk, prePost?, arrow?]

@[builtin_fmt Lean.Parser.Attr.grindSym]
public def fmtGrindSym : Fmt := fun
  | `(Parser.Attr.grindSym| symbol%$symbolTk $p:prio) => do
    let symbolTk ← fmt symbolTk
    let p ← fmt p
    return Layouts.pseudoApplication #[symbolTk, p]
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Attr.grindMod]
public def fmtGrindMod : Fmt := fun
  | `(Parser.Attr.grindMod| $m:grind_mod) => fmt m
  | _ => throw .partialFormatter

@[builtin_fmt Lean.Parser.Attr.grind]
public def fmtGrindAttr : Fmt := fun
  | `(Parser.Attr.grind| grind%$grindTk $[$mod?:grindMod]?) => do
    let grindTk ← fmt grindTk
    let mod? ← fmt? mod?
    return Layouts.pseudoApplication #[grindTk, mod?]
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Attr.«grind!»]
public def fmtGrindBangAttr : Fmt := fun
  | `(Parser.Attr.«grind!»| grind!%$grindTk $[$mod?:grindMod]?) => do
    let grindTk ← fmt grindTk
    let mod? ← fmt? mod?
    return Layouts.pseudoApplication #[grindTk, mod?]
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Attr.«grind?»]
public def fmtGrindQuestionAttr : Fmt := fun
  | `(Parser.Attr.«grind?»| grind?%$grindTk $[$mod?:grindMod]?) => do
    let grindTk ← fmt grindTk
    let mod? ← fmt? mod?
    return Layouts.pseudoApplication #[grindTk, mod?]
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Attr.«grind!?»]
public def fmtGrindBangQuestionAttr : Fmt := fun
  | `(Parser.Attr.«grind!?»| grind!?%$grindTk $[$mod?:grindMod]?) => do
    let grindTk ← fmt grindTk
    let mod? ← fmt? mod?
    return Layouts.pseudoApplication #[grindTk, mod?]
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Attr.lia]
public def fmtLiaAttr : Fmt := fun
  | `(Parser.Attr.lia| lia%$liaTk $[$mod?:grindMod]?) => do
    let liaTk ← fmt liaTk
    let mod? ← fmt? mod?
    return Layouts.pseudoApplication #[liaTk, mod?]
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Attr.lia!]
public def fmtLiaBangAttr : Fmt := fun
  | `(Parser.Attr.lia!| lia!%$liaTk $[$mod?:grindMod]?) => do
    let liaTk ← fmt liaTk
    let mod? ← fmt? mod?
    return Layouts.pseudoApplication #[liaTk, mod?]
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Attr.lia?]
public def fmtLiaQuestionAttr : Fmt := fun
  | `(Parser.Attr.lia?| lia?%$liaTk $[$mod?:grindMod]?) => do
    let liaTk ← fmt liaTk
    let mod? ← fmt? mod?
    return Layouts.pseudoApplication #[liaTk, mod?]
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Attr.lia!?]
public def fmtLiaBangQuestionAttr : Fmt := fun
  | `(Parser.Attr.lia!?| lia!?%$liaTk $[$mod?:grindMod]?) => do
    let liaTk ← fmt liaTk
    let mod? ← fmt? mod?
    return Layouts.pseudoApplication #[liaTk, mod?]
  | _ =>
    throw .partialFormatter
