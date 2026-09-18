/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Marc Huisinga
-/
module

prelude
public import Lean.Fmt.FmtM.Basic
meta import Std.Internal.Order.OfProp
import Init.Data

namespace Lean.Fmt

open Lean.Order in
@[builtin_fmt Lean.Order.«term⌜_⌝»]
public def fmtLatticeOfProp : Fmt := fun
  | `(⌜%$lbTk $p:term ⌝%$rbTk) => do
    let lbTk ← fmt lbTk
    let p ← fmt p
    let rbTk ← fmt rbTk
    return Layouts.parens lbTk p rbTk
  | _ =>
    throw .partialFormatter
