/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Marc Huisinga
-/
module

prelude
public import Lean.Fmt.FmtM.Basic
public import Lean.Fmt.Formatters.Lean.Parser.Term
meta import Init.BinderPredicates
import Init.Data

namespace Lean.Fmt

@[builtin_fmt Lean.«termSatisfies_binder_pred%__»]
public def fmtSatisfiesBinderPred : Fmt := fun
  | `(satisfies_binder_pred%%$satisfiesBinderPredTk $lhs:term $pred:binderPred) => do
    let satisfiesBinderPredTk ← fmt satisfiesBinderPredTk
    let pred ← fmtWithBinderPred lhs pred
    return Layouts.pseudoApplication #[satisfiesBinderPredTk, pred]
  | _ => throw .partialFormatter

public def fmtBinderPredPrefix (opTk rhs : Syntax) : FmtM TaggedDoc := do
  let opTk ← fmt opTk
  let rhs ← fmt rhs
  return Layouts.prefixOperator opTk rhs .withSpacing

@[builtin_fmt Lean.«binderPred>_»]
public def fmtBinderPredGt : Fmt := fun
  | `(binderPred| >%$opTk $rhs:term) => fmtBinderPredPrefix opTk rhs
  | _ => throw .partialFormatter

@[builtin_fmt Lean.«binderPred≥_»]
public def fmtBinderPredGe : Fmt := fun
  | `(binderPred| ≥%$opTk $rhs:term) => fmtBinderPredPrefix opTk rhs
  | _ => throw .partialFormatter

@[builtin_fmt Lean.«binderPred<_»]
public def fmtBinderPredLt : Fmt := fun
  | `(binderPred| <%$opTk $rhs:term) => fmtBinderPredPrefix opTk rhs
  | _ => throw .partialFormatter

@[builtin_fmt Lean.«binderPred≤_»]
public def fmtBinderPredLe : Fmt := fun
  | `(binderPred| ≤%$opTk $rhs:term) => fmtBinderPredPrefix opTk rhs
  | _ => throw .partialFormatter

@[builtin_fmt Lean.«binderPred≠_»]
public def fmtBinderPredNe : Fmt := fun
  | `(binderPred| ≠%$opTk $rhs:term) => fmtBinderPredPrefix opTk rhs
  | _ => throw .partialFormatter

@[builtin_fmt Lean.«binderPred∈_»]
public def fmtBinderPredMem : Fmt := fun
  | `(binderPred| ∈%$opTk $rhs:term) => fmtBinderPredPrefix opTk rhs
  | _ => throw .partialFormatter

@[builtin_fmt Lean.«binderPred∉_»]
public def fmtBinderPredNotMem : Fmt := fun
  | `(binderPred| ∉%$opTk $rhs:term) => fmtBinderPredPrefix opTk rhs
  | _ => throw .partialFormatter

@[builtin_fmt Lean.«binderPred⊆_»]
public def fmtBinderPredSubset : Fmt := fun
  | `(binderPred| ⊆%$opTk $rhs:term) => fmtBinderPredPrefix opTk rhs
  | _ => throw .partialFormatter

@[builtin_fmt Lean.«binderPred⊂_»]
public def fmtBinderPredSSubset : Fmt := fun
  | `(binderPred| ⊂%$opTk $rhs:term) => fmtBinderPredPrefix opTk rhs
  | _ => throw .partialFormatter

@[builtin_fmt Lean.«binderPred⊇_»]
public def fmtBinderPredSuperset : Fmt := fun
  | `(binderPred| ⊇%$opTk $rhs:term) => fmtBinderPredPrefix opTk rhs
  | _ => throw .partialFormatter

@[builtin_fmt Lean.«binderPred⊃_»]
public def fmtBinderPredSSuperset : Fmt := fun
  | `(binderPred| ⊃%$opTk $rhs:term) => fmtBinderPredPrefix opTk rhs
  | _ => throw .partialFormatter

@[builtin_quantifier_fmt Lean.«term∀__,_»]
public def fmtForallBinderPred : QuantifierFmt := fun
  | `(∀%$forallTk $x:binderIdent $pred:binderPred ,%$commaTk $body:term) =>
    some {
      quantifier := forallTk
      binders := .pred x pred
      typeAscriptionTk? := none
      type? := none
      commaTk
      body
    }
  | _ => none

@[builtin_quantifier_fmt Lean.«term∃__,_»]
public def fmtExistsBinderPred : QuantifierFmt := fun
  | `(∃%$existsTk $x:binderIdent $pred:binderPred ,%$commaTk $body:term) =>
    some {
      quantifier := existsTk
      binders := .pred x pred
      typeAscriptionTk? := none
      type? := none
      commaTk
      body
    }
  | _ => none
