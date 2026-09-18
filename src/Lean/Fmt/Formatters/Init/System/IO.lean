/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Marc Huisinga
-/
module

prelude
public import Lean.Fmt.FmtM.Basic
meta import Init.System.IO
import Lean.Fmt.FmtM.CommonFormatters
import Init.Data

namespace Lean.Fmt

@[builtin_fmt «termPrintln!__»]
public def fmtPrintln : Fmt := fun
  | `(println!%$printlnTk $msg:term) => do fmtAppLike #[printlnTk, msg]
  | _ => throw .partialFormatter
