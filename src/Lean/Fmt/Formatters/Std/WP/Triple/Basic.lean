/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Marc Huisinga
-/
module

prelude
public import Lean.Fmt.FmtM.Basic
public import Lean.Fmt.Formatters.Std.Do.Triple.Basic
meta import Std.WP.Triple.Basic
import Lean.Fmt.FmtM.CommonFormatters
import Init.Data

namespace Lean.Fmt

open Std.WP in
@[builtin_fmt Std.WP.tripleNotation]
public def fmtTripleNotation : Fmt := fun
  | `(⦃%$preLbTk $pre ⦄%$preRbTk $[(%$mLbTk? $m?:ident :=%$mColonEqTk? $mVal? )%$mRbTk?]? $prog
      ⦃%$postLbTk $post ⦄%$postRbTk) => do
    let preLbTk ← fmt preLbTk
    let pre ← fmt pre
    let preRbTk ← fmt preRbTk
    let namedArg ← fmtNamedArgumentTerm? mLbTk? m? mColonEqTk? mVal? mRbTk?
    let prog ← fmt prog
    let postLbTk ← fmt postLbTk
    let post ← fmt post
    let postRbTk ← fmt postRbTk
    return hoareTriple preLbTk pre preRbTk namedArg prog postLbTk ⟨#[post]⟩ postRbTk
  | _ => throw .partialFormatter

open Std.WP in
@[builtin_fmt Std.WP.tripleExceptPost]
public def fmtTripleExceptPost : Fmt := fun
  | `(⦃%$preLbTk $pre ⦄%$preRbTk $[(%$mLbTk? $m?:ident :=%$mColonEqTk? $mVal? )%$mRbTk?]? $prog
      ⦃%$postLbTk $post ;%$semicolonTk $epost ⦄%$postRbTk) => do
    let preLbTk ← fmt preLbTk
    let pre ← fmt pre
    let preRbTk ← fmt preRbTk
    let namedArg ← fmtNamedArgumentTerm? mLbTk? m? mColonEqTk? mVal? mRbTk?
    let prog ← fmt prog
    let postLbTk ← fmt postLbTk
    let post ← fmt post
    let semicolonTk ← fmt semicolonTk
    let epost ← fmt epost
    let postRbTk ← fmt postRbTk
    return hoareTriple preLbTk pre preRbTk namedArg prog postLbTk ⟨#[post, semicolonTk, epost]⟩
      postRbTk
  | _ => throw .partialFormatter
