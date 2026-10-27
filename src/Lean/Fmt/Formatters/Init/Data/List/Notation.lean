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

@[builtin_fmt «term%[_|_]»]
public def fmtListLitAux : Fmt := fun
  | `(%[%$lbTk $elems,* |%$pipeTk $tail:term ]%$rbTk) => do
    let lbTk ← fmt lbTk
    let elems ← fmtTSepArray elems
    let pipeTk ← fmt pipeTk
    let tail ← fmt tail
    let rbTk ← fmt rbTk
    let elems := Layouts.sepFill elems
    return Layouts.subtype lbTk elems pipeTk tail rbTk <|
      .sparse «break» (stickynessKind := .coequal)
  | _ =>
    throw .partialFormatter
