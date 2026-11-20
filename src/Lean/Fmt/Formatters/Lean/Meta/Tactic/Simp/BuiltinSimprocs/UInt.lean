/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Marc Huisinga
-/
module

prelude
public import Lean.Fmt.FmtM.Basic
meta import Lean.Meta.Tactic.Simp.BuiltinSimprocs.UInt
import Init.Data

namespace Lean.Fmt

@[builtin_fmt Lean.commandDeclare_uint_simprocs_]
public def fmtDeclareUIntSimprocs : Fmt := fun
  | `(command| declare_uint_simprocs%$declareTk $typeName:ident) => do
    let declareTk ← fmt declareTk
    let typeName ← fmt typeName
    return Layouts.pseudoApplication #[declareTk, typeName]
  | _ => throw .partialFormatter
