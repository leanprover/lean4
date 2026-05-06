/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Marc Huisinga
-/
module

prelude
public import Lean.Fmt.FmtM.Basic
meta import Std.Data.DHashMap.Internal.RawLemmas
import Init.Data

namespace Lean.Fmt

public def fmtSimpToModelLike
    (simpToModelTk : Syntax) (lbTk? : Option Syntax) (names? : Option (Syntax.TSepArray `ident ","))
    (rbTk? : Option Syntax) (usingTk? : Option Syntax) (usingArg? : Option (TSyntax `term))
    : FmtM TaggedDoc := do
  let simpToModelTk ← fmt simpToModelTk
  let lbTk? ← fmt? lbTk?
  let names ← fmtTSepArray (names?.getD ⟨#[]⟩)
  let rbTk? ← fmt? rbTk?
  let usingTk? ← fmt? usingTk?
  let usingArg? ← fmt? usingArg?
  let names := Layouts.collection lbTk? names rbTk?
  let names := propagateStickyness names nested
  let «using» := Layouts.keywordPrefixedTerm usingTk? usingArg? .sticky
  return Layouts.blocks #[simpToModelTk, names, «using»]

open Std.DHashMap.Internal.Raw₀ in
@[builtin_fmt Std.DHashMap.Internal.Raw₀.«tacticSimp_to_model[_]Using_»]
public def fmtHashMapSimpToModel : Fmt := fun
  | `(tactic| simp_to_model%$simpToModelTk $[[%$lbTk? $names?:ident,* ]%$rbTk?]?
      $[using%$usingTk? $usingArg?:term]?) =>
    fmtSimpToModelLike simpToModelTk lbTk? names? rbTk? usingTk? usingArg?
  | _ =>
    throw .partialFormatter
