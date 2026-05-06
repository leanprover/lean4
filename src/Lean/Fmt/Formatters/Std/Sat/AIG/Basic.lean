/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Marc Huisinga
-/
module

prelude
public import Lean.Fmt.FmtM.Basic
meta import Std.Sat.AIG.Basic
import Init.Data

namespace Lean.Fmt

open Std.Sat.AIG in
@[builtin_fmt Std.Sat.AIG.«term⟦_,_⟧»]
public def fmtAIGDenote : Fmt := fun
  | `(⟦%$lbTk $entry:term ,%$commaTk $assign:term ⟧%$rbTk) => do
    let fields : Syntax.TSepArray `term "," := ⟨#[entry, commaTk, assign]⟩
    let lbTk ← fmt lbTk
    let fields ← fmtTSepArray fields
    let rbTk ← fmt rbTk
    return Layouts.tuple lbTk fields rbTk
  | _ => throw .partialFormatter

open Std.Sat.AIG in
@[builtin_fmt Std.Sat.AIG.«term⟦_,_,_⟧»]
public def fmtAIGDenoteEntrypoint : Fmt := fun
  | `(⟦%$lbTk $aig:term ,%$comma₁Tk $ref:term ,%$comma₂Tk $assign:term ⟧%$rbTk) => do
    let fields : Syntax.TSepArray `term "," := ⟨#[aig, comma₁Tk, ref, comma₂Tk, assign]⟩
    let lbTk ← fmt lbTk
    let fields ← fmtTSepArray fields
    let rbTk ← fmt rbTk
    return Layouts.tuple lbTk fields rbTk
  | _ => throw .partialFormatter
