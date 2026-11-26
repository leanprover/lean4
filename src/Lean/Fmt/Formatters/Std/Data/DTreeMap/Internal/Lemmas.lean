/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Marc Huisinga
-/
module

prelude
public import Lean.Fmt.Formatters.Std.Data.DHashMap.Internal.RawLemmas
public import Lean.Fmt.FmtM.Basic
meta import Std.Data.DTreeMap.Internal.Lemmas
import Init.Data

namespace Lean.Fmt

open Std.DTreeMap.Internal.Impl in
@[builtin_fmt Std.DTreeMap.Internal.Impl.«tacticSimp_to_model[_]Using_»]
public def fmtTreeMapSimpToModel : Fmt := fun
  | `(tactic| simp_to_model%$simpToModelTk $[[%$lbTk? $names?:ident,* ]%$rbTk?]?
      $[using%$usingTk? $usingArg?:term]?) =>
    fmtSimpToModelLike simpToModelTk lbTk? names? rbTk? usingTk? usingArg?
  | _ => throw .partialFormatter
