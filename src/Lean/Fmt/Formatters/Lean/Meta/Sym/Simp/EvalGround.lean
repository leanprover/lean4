/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Marc Huisinga
-/
module

prelude
public import Lean.Fmt.FmtM.Basic
meta import Lean.Meta.Sym.Simp.EvalGround
import Init.Data

namespace Lean.Fmt

@[builtin_fmt Lean.Meta.Sym.Simp.commandDeclare_eval_bin__]
public def fmtSimpDeclareEvalBin : Fmt := fun
  | `(Lean.Meta.Sym.Simp.commandDeclare_eval_bin__|
      declare_eval_bin%$declareTk $id:ident $op:term) => do
    let declareTk ← fmt declareTk
    let id ← fmt id
    let op ← fmt op
    return Layouts.pseudoApplication #[declareTk, id, op]
  | _ => throw .partialFormatter

@[builtin_fmt Lean.Meta.Sym.Simp.commandDeclare_eval_bin_bitwise__]
public def fmtSimpDeclareEvalBinBitwise : Fmt := fun
  | `(Lean.Meta.Sym.Simp.commandDeclare_eval_bin_bitwise__|
      declare_eval_bin_bitwise%$declareTk $id:ident $op:term) => do
    let declareTk ← fmt declareTk
    let id ← fmt id
    let op ← fmt op
    return Layouts.pseudoApplication #[declareTk, id, op]
  | _ => throw .partialFormatter

@[builtin_fmt Lean.Meta.Sym.Simp.commandDeclare_eval_bin_bool_pred__]
public def fmtSimpDeclareEvalBinBoolPred : Fmt := fun
  | `(Lean.Meta.Sym.Simp.commandDeclare_eval_bin_bool_pred__|
      declare_eval_bin_bool_pred%$declareTk $id:ident $op:term) => do
    let declareTk ← fmt declareTk
    let id ← fmt id
    let op ← fmt op
    return Layouts.pseudoApplication #[declareTk, id, op]
  | _ => throw .partialFormatter
