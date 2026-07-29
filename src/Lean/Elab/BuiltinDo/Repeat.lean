/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
module

prelude
public import Lean.Elab.BuiltinDo.Basic
meta import Lean.Parser.Do
import Lean.Elab.BuiltinDo.For

public section

namespace Lean.Elab.Do

open Lean.Parser.Term

/--
Builtin do-element elaborator for `repeat` (syntax kind `Lean.Parser.Term.doRepeat`).

Expands to `for _ in Loop.mk do ...`. When the body cannot `break`, the loop's own expression
type is fixed to `PUnit`, yet the surrounding do block may require a different result type;
we append an `unreachable!` so the continuation has a polymorphic value of any type. The
`unreachable!` is never actually executed (the loop never terminates normally), and any
dead-code warning that fires on the surrounding continuation is actionable — the user can
remove the following code without breaking the do block's type.
-/
@[builtin_doElem_elab Lean.Parser.Term.doRepeat] def elabDoRepeat : DoElab := fun stx dec => do
  let `(doElem| repeat%$tk $seq) := stx | throwUnsupportedSyntax
  let mut expanded ← `(doElem| for%$tk _ in Loop.mk do $seq)
  let info ← inferControlInfoSeq seq
  if !info.breaks then
    if !(← Meta.isDefEqGuarded dec.resultType (← mkPUnit)) then
      expanded ← `(doElem| do $expanded:doElem; unreachable!)
  Term.withMacroExpansion stx expanded <|
    withRef expanded <| elabDoElem ⟨expanded⟩ dec

@[builtin_macro Lean.Parser.Term.doWhile] def expandDoWhile : Macro
  | `(doElem| while%$tk $cond:doIfCond do $seq) => `(doElem| repeat%$tk if $cond:doIfCond then $seq else break)
  | _ => Macro.throwUnsupported

/--
Builtin do-element elaborator for `while … invariant` (syntax kind `Lean.Parser.Term.doWhile`).

A `while` without an `invariant` clause is expanded by the macro `expandDoWhile`. The annotated form
expands the same way, but hands the annotation to `elabForLoop`, which rebuilds the loop as the
`Loop.forInWithInvariant` gadget that `vcgen` reads. What holds after such a loop is the invariant
together with the negated loop condition, so control must leave the loop through a failing
condition; `break` and early `return` in the body are rejected.
-/
@[builtin_doElem_elab Lean.Parser.Term.doWhile] def elabDoWhile : DoElab := fun stx dec => do
  let `(doElem| while%$tk $cond:doIfCond $inv:doWhileInvariant do $seq) := stx
    | throwUnsupportedSyntax
  let guard : Term ← match cond with
    | `(doIfProp| $[$_ :]? $guard:term) => pure guard
    | _ => throwErrorAt inv "The `invariant` clause is only supported on a `while` loop whose \
        condition is a proposition."
  let info ← inferControlInfoSeq seq
  if info.breaks || info.returnsEarly then
    throwErrorAt inv "The assertion that holds after a `while` loop with an `invariant` clause is \
      the invariant together with the negated loop condition, so control has to leave the loop \
      through a failing condition. Restructure the body to leave through the loop condition, or \
      drop the `invariant` clause."
  let x ← Term.mkFreshIdent tk
  let body ← `(doSeq| if $cond:doIfCond then $seq else break)
  let expanded ← `(doElem| for%$tk $x:ident in Loop.mk do $body)
  Term.withMacroExpansion stx expanded <| withRef expanded <|
    elabForLoop tk none x (← `(Loop.mk)) body
      (some fun args => mkWhileWithInvariant inv guard args) dec

@[builtin_macro Lean.Parser.Term.doRepeatUntil] def expandDoRepeatUntil : Macro
  | `(doElem| repeat%$tk $seq until $cond) => `(doElem| repeat%$tk do $seq:doSeq; if $cond then break)
  | _ => Macro.throwUnsupported

end Lean.Elab.Do
