/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Marc Huisinga
-/
module

prelude
public import Lean.Fmt.FmtM.Basic
meta import Init.Data.List.Notation
import Lean.Fmt.FmtM.CommonFormatters
import Init.Data

namespace Lean.Fmt

@[builtin_fmt «term[_]»]
public def fmtListLit : Fmt := fun
  | `([%$lbTk $elems,* ]%$rbTk) => fmtArrayLit lbTk elems rbTk
  | _ => throw .partialFormatter

@[builtin_fmt listTreeLit]
public def fmtListTreeLit : Fmt := fun
  | `(%[%$lbTk $elems,* ]%$rbTk) => fmtArrayLit lbTk elems rbTk
  | _ => throw .partialFormatter
