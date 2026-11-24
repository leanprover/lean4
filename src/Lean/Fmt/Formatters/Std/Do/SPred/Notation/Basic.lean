/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Marc Huisinga
-/
module

prelude
public import Lean.Fmt.FmtM.Basic
meta import Std.Do.SPred.Notation.Basic
import Init.Data

namespace Lean.Fmt

open Std.Do in
@[builtin_fmt Std.Do.«termSpred(_)»]
public def fmtSPred : Fmt := fun
  | `(spred(%$lbTk $p:term )%$rbTk) => do
    let lbTk ← fmt lbTk
    let p ← fmt p
    let rbTk ← fmt rbTk
    return Layouts.metaApplication lbTk #[.elems #[p]] rbTk
  | _ => throw .partialFormatter

open Std.Do in
@[builtin_fmt Std.Do.«termTerm(_)»]
public def fmtSPredTermEscape : Fmt := fun
  | `(term(%$lbTk $t:term )%$rbTk) => do
    let lbTk ← fmt lbTk
    let t ← fmt t
    let rbTk ← fmt rbTk
    return Layouts.metaApplication lbTk #[.elems #[t]] rbTk
  | _ => throw .partialFormatter
