/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Marc Huisinga
-/
module

prelude
public import Lean.Fmt.FmtM.Basic
meta import Std.Do.PostCond
import Init.Data

namespace Lean.Fmt

open Std.Do in
@[builtin_fmt Std.Do.«termPost⟨_,,⟩»]
public def fmtPostCond : Fmt := fun
  | `(post⟨%$lbTk $handlers,* ⟩%$rbTk) => do
    let lbTk ← fmt lbTk
    let handlers ← fmtTSepArray handlers
    let rbTk ← fmt rbTk
    return Layouts.metaApplication lbTk (Layouts.metaApplication.Term.ofSepArray handlers) rbTk
  | _ => throw .partialFormatter

open Std.Do in
@[builtin_fmt Std.Do.«term_⇓_=>_»]
public def fmtNoThrowPostCond : Fmt := fun
  | `(⇓%$noThrowTk $xs:term* =>%$arrowTk $p:term) => do
    let noThrowTk ← fmt noThrowTk
    let xs ← fmtArray xs
    let arrowTk ← fmt arrowTk
    let p ← fmt p
    let signature := Layouts.prefixOperator noThrowTk (Layouts.fill xs) .withSpacing
    return Layouts.assignmentDeclaration (sticky := true) signature arrowTk p
  | _ => throw .partialFormatter

open Std.Do in
@[builtin_fmt Std.Do.«term_⇓?_=>_»]
public def fmtMayThrowPostCond : Fmt := fun
  | `(⇓?%$mayThrowTk $xs:term* =>%$arrowTk $p:term) => do
    let mayThrowTk ← fmt mayThrowTk
    let xs ← fmtArray xs
    let arrowTk ← fmt arrowTk
    let p ← fmt p
    let signature := Layouts.prefixOperator mayThrowTk (Layouts.fill xs) .withSpacing
    return Layouts.assignmentDeclaration (sticky := true) signature arrowTk p
  | _ => throw .partialFormatter
