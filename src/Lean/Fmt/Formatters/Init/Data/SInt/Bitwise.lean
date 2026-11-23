/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Marc Huisinga
-/
module

prelude
public import Lean.Fmt.FmtM.Basic
meta import Init.Data.SInt.Bitwise
import Lean.Fmt.FmtM.CommonFormatters
import Init.Data

namespace Lean.Fmt

@[builtin_fmt commandDeclare_bitwise_int_theorems__]
public def fmtDeclareBitwiseIntTheorems : Fmt := fun
  | `(command| declare_bitwise_int_theorems%$tk $typeName:ident $bits:term) => do
    let tk ← fmt tk
    let typeName ← fmt typeName
    let bits ← fmt bits
    return Layouts.pseudoApplication #[tk, typeName, bits]
  | _ => throw .partialFormatter
