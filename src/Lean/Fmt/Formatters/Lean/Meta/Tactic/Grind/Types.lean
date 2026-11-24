/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Marc Huisinga
-/
module

prelude
public import Lean.Fmt.FmtM.Basic
public import Lean.Fmt.Formatters.Lean.Util.Trace
meta import Lean.Meta.Tactic.Grind.Types
import Init.Data

namespace Lean.Fmt

@[builtin_fmt Lean.Meta.Grind.«doElemTrace_goal[_]__»]
public def fmtDoElemTraceGoal : Fmt := fun
  | `(doElem| trace_goal[%$traceGoalTk $traceCls:ident ]%$rbTk $msg) => do
    let traceGoalTk ← fmt traceGoalTk
    let traceCls ← fmt traceCls
    let rbTk ← fmt rbTk
    let traceClass := Layouts.bracketed traceGoalTk traceCls rbTk .dense
    fmtTraceTerm traceClass msg
  | _ => throw .partialFormatter
