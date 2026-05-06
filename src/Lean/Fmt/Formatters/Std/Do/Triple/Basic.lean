/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Marc Huisinga
-/
module

prelude
public import Lean.Fmt.FmtM.Basic
meta import Std.Do.Triple.Basic
import Init.Data

namespace Lean.Fmt

/--
Layout for Hoare triples `⦃ pre ⦄ namedArg prog ⦃ post ⦄`, where `namedArg` is an optional
argument such as a monad ascription and `post` may consist of several components, e.g. a binder
for the return value, the postcondition and an exception postcondition.

Since the separator string of `post` is merely a fallback for elements without a separator
document, `post` may use a mix of separators such as `,` and `;`.
-/
public def hoareTriple
    (preLbTk pre preRbTk : TaggedDoc) (namedArg : TaggedDoc) (prog : TaggedDoc)
    (postLbTk : TaggedDoc) (post : SepArray ";") (postRbTk : TaggedDoc)
    : TaggedDoc :=
  let pre := Layouts.tuple preLbTk (sep := ";") ⟨#[pre]⟩ preRbTk
  let post := Layouts.tuple postLbTk post postRbTk
  Layouts.horizontalOrVertical #[Layouts.pseudoApplication #[pre, namedArg], prog, post]

open Std.Do in
@[builtin_fmt Std.Do.triple]
public def fmtTriple : Fmt := fun
  | `(⦃%$preLbTk $pre ⦄%$preRbTk $prog ⦃%$postLbTk $post ⦄%$postRbTk) => do
    let preLbTk ← fmt preLbTk
    let pre ← fmt pre
    let preRbTk ← fmt preRbTk
    let prog ← fmt prog
    let postLbTk ← fmt postLbTk
    let post ← fmt post
    let postRbTk ← fmt postRbTk
    return hoareTriple preLbTk pre preRbTk empty prog postLbTk ⟨#[post]⟩ postRbTk
  | _ =>
    throw .partialFormatter
