/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Marc Huisinga
-/
module

prelude
public import Lean.Fmt.FmtM.Basic
meta import Init.Data.Array.Basic
import Lean.Fmt.FmtM.CommonFormatters
import Init.Data

namespace Lean.Fmt

@[builtin_fmt «term#[_,]»]
public def fmtArrayLiteral : Fmt := fun
  | `(#[%$lbTk $elems,* ]%$rbTk) => do fmtArrayLit lbTk elems rbTk
  | _ => throw .partialFormatter
