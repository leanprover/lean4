/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Marc Huisinga
-/
module

prelude
public import Lean.Fmt.FmtM.Basic
meta import Init.MacroTrace
import Init.Data

namespace Lean.Fmt

@[builtin_fmt Lean.«termMacro.trace[_]_»]
public def fmtMacroTrace : Fmt := fun
  | `(Macro.trace[%$lbTk $id:ident ]%$rbTk $msg:interpolatedStr) => do
    let lbTk ← fmt lbTk
    let id ← fmt id
    let rbTk ← fmt rbTk
    let msg ← fmt msg
    let traceClass := Layouts.bracketed lbTk id rbTk .dense
    return Layouts.pseudoApplication #[traceClass, msg]
  | _ => throw .partialFormatter
