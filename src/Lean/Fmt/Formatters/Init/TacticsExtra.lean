/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Marc Huisinga
-/
module

prelude
public import Lean.Fmt.FmtM.Basic
meta import Init.TacticsExtra
import Lean.Fmt.FmtM.CommonFormatters
import Init.Data

namespace Lean.Fmt

@[builtin_fmt Lean.Parser.Tactic.tacticIterate____]
public def fmtIterate : Fmt := fun
  | `(tactic| iterate%$iterateTk $[$n?:num]? $seq:tacticSeq) => do
    let iterateTk ← fmt iterateTk
    let n? ← fmt? n?
    let lhs := Layouts.pseudoApplication #[iterateTk, n?]
    let seq ← fmt seq
    return Layouts.keywordPrefixedSeq lhs seq .nonSticky
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.tacticRw_mod_cast___]
public def fmtRwModCast : Fmt := fun
  | `(tactic| rw_mod_cast%$rwTk $cfg:optConfig $rules:rwRuleSeq $[$loc?:location]?) => do
    fmtRwLike rwTk cfg rules loc?
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.tacticExact_mod_cast_]
public def fmtExactModCast : Fmt := fun
  | `(tactic| exact_mod_cast%$exactTk $e:term) => do
    let exactTk ← fmt exactTk
    let e ← fmt e
    return Layouts.pseudoApplication #[exactTk, e]
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.tacticApply_mod_cast_]
public def fmtApplyModCast : Fmt := fun
  | `(tactic| apply_mod_cast%$applyTk $e:term) => do
    let applyTk ← fmt applyTk
    let e ← fmt e
    return Layouts.pseudoApplication #[applyTk, e]
  | _ =>
    throw .partialFormatter
