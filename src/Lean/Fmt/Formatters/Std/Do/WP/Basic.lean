/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Marc Huisinga
-/
module

prelude
public import Lean.Fmt.FmtM.Basic
meta import Std.Do.WP.Basic
import Init.Data

namespace Lean.Fmt

open Std.Do in
@[builtin_fmt Std.Do.«termWp⟦_:_⟧»]
public def fmtWP : Fmt := fun
  | `(wp⟦%$lbTk $x:term $[ :%$typeAscriptionTk? $type? ]?⟧%$rbTk) => do
    let lbTk ← fmt lbTk
    let x ← fmt x
    let typeAscriptionTk? ← fmt? typeAscriptionTk?
    let type? ← fmt? type?
    let rbTk ← fmt rbTk
    let body := Layouts.typeAscription x typeAscriptionTk? type?
    return Layouts.parens lbTk body rbTk
  | _ => throw .partialFormatter
