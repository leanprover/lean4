/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Marc Huisinga
-/
module

prelude
public import Lean.Fmt.FmtM.Basic
meta import Init.Data.BitVec.Basic
import Init.Data

namespace Lean.Fmt

open scoped BitVec

@[builtin_fmt BitVec.«term__#__»]
public def fmtBitVecLit : Fmt := fun
  | `(BitVec.«term__#__»| $i:num#%$hashTk$n:term) => do
    let i ← fmt i
    let hashTk ← fmt hashTk
    let n ← fmt n
    return mkSelfDelimited <| Layouts.atomicInfixOperator #[i, hashTk, n]
  | _ => throw .partialFormatter

@[builtin_fmt BitVec.«term__#'__»]
public def fmtBitVecLitLT : Fmt := fun
  | `($i#'%$hashTk$p) => do
    let i ← fmt i
    let hashTk ← fmt hashTk
    let p ← fmt p
    return mkSelfDelimited <| Layouts.atomicInfixOperator #[i, hashTk, p]
  | _ => throw .partialFormatter
