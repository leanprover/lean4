/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Marc Huisinga
-/
module

prelude
public import Lean.Fmt.FmtM.Basic
meta import Init.Data.SInt.Decidable
import Lean.Fmt.FmtM.CommonFormatters
import Init.Data

namespace Lean.Fmt

@[builtin_fmt commandDeclare_decidable_int_quantifiers__]
public def fmtDeclareDecidableIntQuantifiers : Fmt := fun
  | `(command| declare_decidable_int_quantifiers%$tk $typeName:ident $bits:term) => do
    let tk ← fmt tk
    let typeName ← fmt typeName
    let bits ← fmt bits
    return Layouts.pseudoApplication #[tk, typeName, bits]
  | _ => throw .partialFormatter
