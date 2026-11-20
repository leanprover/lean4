/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Marc Huisinga
-/
module

prelude
public import Lean.Fmt.FmtM.Basic
meta import Lean.PrettyPrinter.Delaborator.Basic
import Init.Data

namespace Lean.Fmt

@[builtin_fmt Lean.PrettyPrinter.Delaborator.attrApp_delab_]
public def fmtAppDelab : Fmt := fun
  | `(Lean.PrettyPrinter.Delaborator.attrApp_delab_| app_delab%$appDelabTk $id:ident) => do
    let appDelabTk ← fmt appDelabTk
    let id ← fmt id
    return Layouts.pseudoApplication #[appDelabTk, id]
  | _ => throw .partialFormatter
