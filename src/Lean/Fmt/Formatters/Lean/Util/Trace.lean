/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Marc Huisinga
-/
module

prelude
public import Lean.Fmt.FmtM.Basic
meta import Lean.Util.Trace
import Init.Data

namespace Lean.Fmt

/-- Attaches the message of a `trace[...]`-like instruction to the instruction's keyword. -/
public def fmtTraceTerm (keyword : TaggedDoc) (msg : Syntax) : FmtM TaggedDoc := do
  let msg ← fmt msg
  return Layouts.pseudoApplication #[keyword, msg]

@[builtin_fmt Lean.«doElemTrace[_]__»]
public def fmtDoElemTrace : Fmt := fun
  | `(doElem| trace[%$traceTk $traceCls:ident ]%$rbTk $msg) => do
    let traceTk ← fmt traceTk
    let traceCls ← fmt traceCls
    let rbTk ← fmt rbTk
    let traceClass := Layouts.bracketed traceTk traceCls rbTk .dense
    fmtTraceTerm traceClass msg
  | _ => throw .partialFormatter
