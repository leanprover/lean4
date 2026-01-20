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
  elabNestedActions (e?.getD ⟨.missing⟩) fun e => do
  -- When using the ControlLifter framework, `returnCont.resultType` can be different than the
  -- result type of the `do` block. That's why we track it separately.
  let e ← match e.raw with
    | .missing => Term.ensureHasType returnCont.resultType (← mkPUnitUnit)
    | _        => Term.elabTermEnsuringType e returnCont.resultType
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

@[builtin_doElem_elab Lean.Parser.Term.doExpr] def elabDoExpr : DoElab := fun stx dec => do
  let `(doExpr| $e:term) := stx | throwUnsupportedSyntax
  let mα ← mkMonadicType dec.resultType
  elabNestedActions e fun e => do
  let e ← Term.elabTermEnsuringType e mα
  dec.mkBindUnlessPure stx e

@[builtin_doElem_elab Lean.Parser.Term.doNested] def elabDoNested : DoElab := fun stx dec => do
  let `(doNested| do $doSeq) := stx | throwUnsupportedSyntax
  elabDoSeq ⟨doSeq.raw⟩ dec

@[builtin_doElem_elab Lean.Parser.Term.doUnless] def elabDoUnless : DoElab := fun stx dec => do
  let `(doUnless| unless $cond do $body) := stx | throwUnsupportedSyntax
  elabDoElem (← `(doElem| if $cond then pure PUnit.unit else $body)) dec

@[builtin_doElem_elab Lean.Parser.Term.doDbgTrace] def elabDoDbgTrace : DoElab := fun stx dec => do
  let `(doDbgTrace| dbg_trace $msg:term) := stx | throwUnsupportedSyntax
  let mγ ← mkMonadicType (← read).doBlockResultType
  let body ← dec.continueWithUnit stx
  let body ← Term.exprToSyntax body
  elabNestedActions msg fun msg => do
  Term.elabTerm (← `(dbg_trace $msg; $body)) mγ

@[builtin_doElem_elab Lean.Parser.Term.doAssert] def elabDoAssert : DoElab := fun stx dec => do
  let `(doAssert| assert! $cond) := stx | throwUnsupportedSyntax
  let mγ ← mkMonadicType (← read).doBlockResultType
  let body ← dec.continueWithUnit stx
  let body ← Term.exprToSyntax body
  elabNestedActions cond fun cond => do
  Term.elabTerm (← `(assert! $cond; $body)) mγ

@[builtin_doElem_elab Lean.Parser.Term.doDebugAssert] def elabDoDebugAssert : DoElab := fun stx dec => do
  let `(doDebugAssert| debug_assert! $cond) := stx | throwUnsupportedSyntax
  let mγ ← mkMonadicType (← read).doBlockResultType
  let body ← dec.continueWithUnit stx
  let body ← Term.exprToSyntax body
  elabNestedActions cond fun cond => do
  Term.elabTerm (← `(debug_assert! $cond; $body)) mγ
