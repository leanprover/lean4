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

Expands to `for _ in Loop.mk do ...`, carrying the loop's clauses over to the `for` loop. When the
body cannot `break`, the loop's own expression type is fixed to `PUnit`, yet the surrounding do
block may require a different result type; we append an `unreachable!` so the continuation has a
polymorphic value of any type. The `unreachable!` is never actually executed (the loop never
terminates normally), and any dead-code warning that fires on the surrounding continuation is
actionable — the user can remove the following code without breaking the do block's type.
-/
@[builtin_doElem_elab Lean.Parser.Term.doRepeat] def elabDoRepeat : DoElab := fun stx dec => do
  -- The `do` before the body is there exactly when the loop carries a clause.
  let some (tk, inv?, var?, seq) := (match stx with
      | `(doElem| repeat%$tk $[$inv?:doForInvariant]? $[$var?:doDecreasing]? do $seq)
      | `(doElem| repeat%$tk $[$inv?:doForInvariant]? $[$var?:doDecreasing]? $seq:doSeq) =>
        some (tk, inv?, var?, seq)
      | _ => none)
    | throwUnsupportedSyntax
  let mut expanded ←
    `(doElem| for%$tk _ in Loop.mk $[$inv?:doForInvariant]? $[$var?:doDecreasing]? do $seq)
  let info ← inferControlInfoSeq seq
  if !info.breaks then
    if !(← Meta.isDefEqGuarded dec.resultType (← mkPUnit)) then
      expanded ← `(doElem| do $expanded:doElem; unreachable!)
  Term.withMacroExpansion stx expanded <|
    withRef expanded <| elabDoElem ⟨expanded⟩ dec

@[builtin_macro Lean.Parser.Term.doWhile] def expandDoWhile : Macro
  | `(doElem| while%$tk $cond:doIfCond $[$inv?:doForInvariant]? $[$dec?:doDecreasing]? do $seq) =>
    `(doElem| repeat%$tk $[$inv?:doForInvariant]? $[$dec?:doDecreasing]? do
        if $cond:doIfCond then $seq else break)
  | _ => Macro.throwUnsupported

@[builtin_macro Lean.Parser.Term.doRepeatUntil] def expandDoRepeatUntil : Macro
  | `(doElem| repeat%$tk $[$inv?:doForInvariant]? $[$dec?:doDecreasing]? do $seq until $cond)
  | `(doElem| repeat%$tk $[$inv?:doForInvariant]? $[$dec?:doDecreasing]? $seq:doSeq until $cond) =>
    `(doElem| repeat%$tk $[$inv?:doForInvariant]? $[$dec?:doDecreasing]? do
        do $seq:doSeq
        if $cond then break)
  | _ => Macro.throwUnsupported

end Lean.Elab.Do
