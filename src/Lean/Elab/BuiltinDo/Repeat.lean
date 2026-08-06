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

/-- Split a `doLoopClauses` node into the `invariant` and `decreasing` clauses it carries. Either
clause may be given on its own, so the node's children are inspected by kind. -/
def splitLoopClauses (clauses? : Option Syntax) :
    Option (TSyntax ``doForInvariant) × Option (TSyntax ``doDecreasing) := Id.run do
  let some clauses := clauses? | return (none, none)
  let mut inv? := none
  let mut dec? := none
  for arg in clauses.getArgs do
    let arg := if arg.isOfKind nullKind then arg.getArgs.getD 0 .missing else arg
    if arg.isOfKind ``doForInvariant then
      inv? := some ⟨arg⟩
    else if arg.isOfKind ``doDecreasing then
      dec? := some ⟨arg⟩
  return (inv?, dec?)

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
  let `(doElem| repeat%$tk $[$clauses?:doLoopClauses]? $seq) := stx | throwUnsupportedSyntax
  let (inv?, var?) := splitLoopClauses (clauses?.map (·.raw))
  let mut expanded ←
    `(doElem| for%$tk _ in Loop.mk $[$inv?:doForInvariant]? $[$var?:doDecreasing]? do $seq)
  let info ← inferControlInfoSeq seq
  if !info.breaks then
    if !(← Meta.isDefEqGuarded dec.resultType (← mkPUnit)) then
      expanded ← `(doElem| do $expanded:doElem; unreachable!)
  Term.withMacroExpansion stx expanded <|
    withRef expanded <| elabDoElem ⟨expanded⟩ dec

@[builtin_macro Lean.Parser.Term.doWhile] def expandDoWhile : Macro
  | `(doElem| while%$tk $cond:doIfCond $[$inv?:doForInvariant]? $[$dec?:doDecreasing]? do $seq) => do
    let body ← `(doSeq| if $cond:doIfCond then $seq else break)
    match inv?, dec? with
    | none, none => `(doElem| repeat%$tk $body:doSeq)
    | some inv, none => `(doElem| repeat%$tk $inv:doForInvariant do $body:doSeq)
    | none, some dec => `(doElem| repeat%$tk $dec:doDecreasing do $body:doSeq)
    | some inv, some dec =>
      `(doElem| repeat%$tk $inv:doForInvariant $dec:doDecreasing do $body:doSeq)
  | _ => Macro.throwUnsupported

@[builtin_macro Lean.Parser.Term.doRepeatUntil] def expandDoRepeatUntil : Macro
  | `(doElem| repeat%$tk $[$clauses?:doLoopClauses]? $seq until $cond) => do
    let body ← `(doSeq| do $seq:doSeq
                        if $cond then break)
    `(doElem| repeat%$tk $[$clauses?:doLoopClauses]? $body:doSeq)
  | _ => Macro.throwUnsupported

end Lean.Elab.Do
