/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Marc Huisinga
-/
module

prelude
public import Lean.Fmt.FmtM.Basic
public import Lean.Fmt.Formatters.Init.Simproc
meta import Init.Grind.Propagator
import Lean.Fmt.FmtM.CommonFormatters
import Init.Data

namespace Lean.Fmt

@[builtin_fmt Lean.Parser.«command_Grind_propagator___(_):=_»]
public def fmtGrindPropagator : Fmt := fun
  | `(command|
      $[$docComment?:docComment]?
      grind_propagator%$grindPropagatorTk $direction $declId:ident
        (%$lparenTk $op:ident )%$rparenTk :=%$colonEqTk $body:term) =>
    fmtSimprocLike docComment? #[] grindPropagatorTk direction none none none declId lparenTk op
      rparenTk colonEqTk body
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.«command_Builtin_grind_propagator____:=_»]
public def fmtBuiltinGrindPropagator : Fmt := fun
  | `(command|
      $[$docComment?:docComment]?
      builtin_grind_propagator%$builtinGrindPropagatorTk $declId:ident $direction
        $op:ident :=%$colonEqTk $body:term) => do
    let builtinGrindPropagatorTk ← fmt builtinGrindPropagatorTk
    let declId ← fmt declId
    let direction ← fmt direction
    let op ← fmt op
    let colonEqTk ← fmt colonEqTk
    let body ← fmt body
    let trigger := Layouts.prefixOperator direction op .withSpacing
    let signature := Layouts.pseudoApplication #[builtinGrindPropagatorTk, declId, trigger]
    let decl := Layouts.assignmentDeclaration signature colonEqTk body
    fmtDeclWithModifiers docComment? none #[] decl
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.grindPropagatorBuiltinAttr]
public def fmtGrindPropagatorBuiltinAttr : Fmt := fun
  | `(Parser.grindPropagatorBuiltinAttr|
      builtin_grind_propagator%$builtinGrindPropagatorTk $direction $op:ident) => do
    let builtinGrindPropagatorTk ← fmt builtinGrindPropagatorTk
    let direction ← fmt direction
    let op ← fmt op
    let keyword := Layouts.spacedAtomic #[builtinGrindPropagatorTk, direction]
    return Layouts.pseudoApplication #[keyword, op]
  | _ =>
    throw .partialFormatter
