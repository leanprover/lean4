/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Marc Huisinga
-/
module

prelude
public import Lean.Fmt.FmtM.Basic
meta import Std.Data.DHashMap.RawLemmas
import Init.Data

namespace Lean.Fmt

open Std.DHashMap.Internal.Raw in
@[builtin_fmt Std.DHashMap.Internal.Raw.tacticSimp_to_rawUsing_]
public def fmtSimpToRaw : Fmt := fun
  | `(tactic| simp_to_raw%$simpToRawTk $[using%$usingTk? $usingArg?:term]?) => do
    let simpToRawTk ← fmt simpToRawTk
    let usingTk? ← fmt? usingTk?
    let usingArg? ← fmt? usingArg?
    let «using» := Layouts.keywordPrefixedTerm usingTk? usingArg? .sticky
    return Layouts.blocks #[simpToRawTk, «using»]
  | _ => throw .partialFormatter
