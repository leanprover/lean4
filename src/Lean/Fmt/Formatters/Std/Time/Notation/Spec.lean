/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Marc Huisinga
-/
module

prelude
public import Lean.Fmt.FmtM.Basic
meta import Std.Time.Notation.Spec
import Init.Data

namespace Lean.Fmt

@[builtin_fmt Std.Time.«termDatespec(_)»]
public def fmtDatespec : Fmt := fun
  | `(datespec(%$lbTk $spec:str )%$rbTk) => do
    let lbTk ← fmt lbTk
    let spec ← fmt spec
    let rbTk ← fmt rbTk
    return Layouts.metaApplication lbTk #[.elems #[spec]] rbTk
  | _ => throw .partialFormatter

@[builtin_fmt Std.Time.«termDatespec(_,_)»]
public def fmtDatespecWithConfig : Fmt := fun
  | `(datespec(%$lbTk $spec:str ,%$commaTk $config:term )%$rbTk) => do
    let lbTk ← fmt lbTk
    let spec ← fmt spec
    let commaTk ← fmt commaTk
    let config ← fmt config
    let rbTk ← fmt rbTk
    return Layouts.metaApplication lbTk #[.elems #[spec], .sep commaTk, .elems #[config]] rbTk
  | _ => throw .partialFormatter
