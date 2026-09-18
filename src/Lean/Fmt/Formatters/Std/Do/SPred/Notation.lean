/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Marc Huisinga
-/
module

prelude
public import Lean.Fmt.Formatters.Std.Do.SPred.Notation.Basic
public import Lean.Fmt.FmtM.Basic
meta import Std.Do.SPred.Notation
import Init.Data

namespace Lean.Fmt

open Std.Do in
@[builtin_fmt Std.Do.«term⌜_⌝»]
public def fmtSPredPure : Fmt := fun
  | `(⌜%$lbTk $p:term ⌝%$rbTk) => do
    let lbTk ← fmt lbTk
    let p ← fmt p
    let rbTk ← fmt rbTk
    return Layouts.parens lbTk p rbTk
  | _ =>
    throw .partialFormatter

open Std.Do in
@[builtin_fmt Std.Do.«term⊢ₛ_»]
public def fmtSPredTautology : Fmt := fun
  | `(⊢ₛ%$entailsTk $p:term) => do
    let entailsTk ← fmt entailsTk
    let p ← fmt p
    return Layouts.prefixOperator entailsTk p .withSpacing
  | _ =>
    throw .partialFormatter

@[builtin_infix_fmt Std.Do.«term_⊣⊢ₛ_»]
public def fmtSPredBientails : Fmt.InfixOperation := {
  sparse := true
  precs? := some { prec := 25, lhsPrec := 25, rhsPrec := 25 }
}
