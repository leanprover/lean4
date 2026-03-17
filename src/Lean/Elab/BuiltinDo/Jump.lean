/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
module

prelude
public import Lean.Elab.Do.Basic
meta import Lean.Parser.Do

public section

namespace Lean.Elab.Do

open Lean.Parser.Term
open Lean.Meta

@[builtin_doElem_elab Lean.Parser.Term.doReturn] def elabDoReturn : DoElab := fun stx dec => do
  let `(doReturn| return $[$e?]?) := stx | throwUnsupportedSyntax
  let returnCont ← getReturnCont
  -- When using the ControlLifter framework, `returnCont.resultType` can be different than the
  -- result type of the `do` block. That's why we track it separately.
  -- trace[Elab.do] "return e: {e} with type {returnCont.resultType}"
  let e ← match e? with
    | none   => Term.ensureHasType returnCont.resultType (← mkPUnitUnit)
    | some e => Term.elabTermEnsuringType e returnCont.resultType
  dec.elabAsSyntacticallyDeadCode -- emit dead code warnings
  returnCont.k e

@[builtin_doElem_elab Lean.Parser.Term.doBreak] def elabDoBreak : DoElab := fun _stx dec => do
  let some breakCont := (← getBreakCont)
    | throwError "`break` must be nested inside a loop"
  dec.elabAsSyntacticallyDeadCode -- emit dead code warnings
  breakCont

@[builtin_doElem_elab Lean.Parser.Term.doContinue] def elabDoContinue : DoElab := fun _stx dec => do
  let some continueCont := (← getContinueCont)
    | throwError "`continue` must be nested inside a loop"
  dec.elabAsSyntacticallyDeadCode -- emit dead code warnings
  continueCont
