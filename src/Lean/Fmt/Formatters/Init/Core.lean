/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Marc Huisinga
-/
module

prelude
public import Lean.Fmt.FmtM.Basic
meta import Init.Core
import Init.Data

namespace Lean.Fmt

@[builtin_fmt «term{}»]
public def fmtEmptyBraces : Fmt := fun
  | `(«term{}»| {%$lbTk }%$rbTk) => do
    let lbTk ← fmt lbTk
    let rbTk ← fmt rbTk
    return Layouts.atomic #[lbTk, rbTk]
  | _ => throw .partialFormatter
