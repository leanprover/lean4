/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Marc Huisinga
-/
module

prelude
public import Lean.Fmt.FmtM.Basic
public import Lean.Fmt.Formatters.Lean.Util.Trace
meta import Lean.Meta.Sym.SymM
import Init.Data

namespace Lean.Fmt

@[builtin_fmt Lean.Meta.Sym.doElemReportIssue!__]
public def fmtDoElemReportIssue : Fmt := fun
  | `(doElem| reportIssue!%$reportTk $msg) => do
    let reportTk ← fmt reportTk
    fmtTraceTerm reportTk msg
  | _ => throw .partialFormatter

@[builtin_fmt Lean.Meta.Sym.doElemReportDbgIssue!__]
public def fmtDoElemReportDbgIssue : Fmt := fun
  | `(doElem| reportDbgIssue!%$reportTk $msg) => do
    let reportTk ← fmt reportTk
    fmtTraceTerm reportTk msg
  | _ => throw .partialFormatter
