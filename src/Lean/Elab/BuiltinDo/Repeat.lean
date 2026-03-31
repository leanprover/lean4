/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
module

prelude
public import Lean.Elab.BuiltinDo.Basic
meta import Lean.Parser.Do
public import Lean.Elab.Do.Switch

public section

namespace Lean.Elab.Do

open Lean.Parser.Term

/--
Builtin do-element elaborator for `repeat` (syntax kind `Lean.Parser.Term.doRepeat`).

When `backward.do.while` is `false` (the default), expands to `for _ in Lean.Repeat.mk do ...`,
which uses `WellFounded.extrinsicFix` and admits verification.
When `backward.do.while` is `true`, expands to `for _ in Lean.Loop.mk do ...`, which uses a
`partial` fixed point and is opaque to the proof system but does not require a `MonadAttach`
instance on the ambient monad.

When the body cannot `break` and the surrounding do block's result type does not unify with
`PUnit`, appends an `unreachable!` so the continuation has a polymorphic value of any type.
The `unreachable!` is never actually executed (the loop never terminates normally), and any
dead-code warning that fires on the surrounding continuation is actionable — the user can
remove the following code without breaking the do block's type.
-/
@[builtin_doElem_elab Lean.Parser.Term.doRepeat] def elabDoRepeat : DoElab := fun stx dec => do
  let `(doElem| repeat%$tk $seq) := stx | throwUnsupportedSyntax
  let mut expanded ←
    if Lean.Elab.Term.backward.do.while.get (← getOptions) then
      `(doElem| for%$tk _ in Lean.Loop.mk do $seq)
    else
      `(doElem| for%$tk _ in Lean.Repeat.mk do $seq)
  let info ← inferControlInfoSeq seq
  if !info.breaks then
    if !(← Meta.isDefEqGuarded dec.resultType (← mkPUnit)) then
      expanded ← `(doElem| do $expanded:doElem; unreachable!)
  Term.withMacroExpansion stx expanded <|
    withRef expanded <| elabDoElem ⟨expanded⟩ dec

@[builtin_macro Lean.Parser.Term.doWhileH] def expandDoWhileH : Macro
  | `(doElem| while%$tk $h : $cond do $seq) => `(doElem| repeat%$tk if $h:ident : $cond then $seq else break)
  | _ => Macro.throwUnsupported

@[builtin_macro Lean.Parser.Term.doWhile] def expandDoWhile : Macro
  | `(doElem| while%$tk $cond do $seq) => `(doElem| repeat%$tk if $cond then $seq else break)
  | _ => Macro.throwUnsupported

@[builtin_macro Lean.Parser.Term.doRepeatUntil] def expandDoRepeatUntil : Macro
  | `(doElem| repeat%$tk $seq until $cond) => `(doElem| repeat%$tk do $seq:doSeq; if $cond then break)
  | _ => Macro.throwUnsupported

end Lean.Elab.Do
