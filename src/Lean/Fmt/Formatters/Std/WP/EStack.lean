/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Marc Huisinga
-/
module

prelude
public import Lean.Fmt.FmtM.Basic
meta import Std.WP.EStack
import Init.Data

namespace Lean.Fmt

open Std.WP in
@[builtin_fmt Std.WP.«termEStack⟨_⟩»]
public def fmtEStackType : Fmt := fun
  | `(EStack⟨%$lbTk $exceptConds,* ⟩%$rbTk) => do
    let lbTk ← fmt lbTk
    let exceptConds ← fmtTSepArray exceptConds
    let rbTk ← fmt rbTk
    return Layouts.metaApplication lbTk (Layouts.metaApplication.Term.ofSepArray exceptConds) rbTk
  | _ => throw .partialFormatter

open Std.WP in
@[builtin_fmt Std.WP.«termEstack⟨_⟩»]
public def fmtEStackValue : Fmt := fun
  | `(estack⟨%$lbTk $handlers,* ⟩%$rbTk) => do
    let lbTk ← fmt lbTk
    let handlers ← fmtTSepArray handlers
    let rbTk ← fmt rbTk
    return Layouts.metaApplication lbTk (Layouts.metaApplication.Term.ofSepArray handlers) rbTk
  | _ => throw .partialFormatter
