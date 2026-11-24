/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Marc Huisinga
-/
module

prelude
public import Lean.Fmt.FmtM.Basic
meta import Init.Data.Int.Basic
import Init.Data

namespace Lean.Fmt

@[builtin_fmt Int.«term-[_+1]»]
public def fmtIntNegSucc : Fmt := fun
  | `(Int.«term-[_+1]»| -[%$lbTk $n:term +1]%$rbTk) => do
    let lbTk ← fmt lbTk
    let n ← fmt n
    let rbTk ← fmt rbTk
    return Layouts.atomicInfixOperator #[lbTk, n, rbTk]
  | _ => throw .partialFormatter
