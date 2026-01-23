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

@[builtin_doElem_elab Lean.Parser.Term.doExpr] def elabDoExpr : DoElab := fun stx dec => do
  let `(doExpr| $e:term) := stx | throwUnsupportedSyntax
  let mα ← mkMonadicType dec.resultType
  elabNestedActions e fun e => do
  -- We need to synthesize here, otherwise we quickly get `match` discriminants with MVar types,
  -- which will bring the constraint system to a halt. Apparently even using `postpone := .partial`
  -- here will report type errors too eagerly.
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
  elabNestedActions msg fun msg => do
  doElabToSyntax "dbg_trace body" (dec.continueWithUnit stx) fun body => do
  Term.elabTerm (← `(dbg_trace $msg; $body)) mγ

@[builtin_doElem_elab Lean.Parser.Term.doAssert] def elabDoAssert : DoElab := fun stx dec => do
  let `(doAssert| assert! $cond) := stx | throwUnsupportedSyntax
  let mγ ← mkMonadicType (← read).doBlockResultType
  elabNestedActions cond fun cond => do
  doElabToSyntax "assert! body" (dec.continueWithUnit stx) fun body => do
  Term.elabTerm (← `(assert! $cond; $body)) mγ

@[builtin_doElem_elab Lean.Parser.Term.doDebugAssert] def elabDoDebugAssert : DoElab := fun stx dec => do
  let `(doDebugAssert| debug_assert! $cond) := stx | throwUnsupportedSyntax
  let mγ ← mkMonadicType (← read).doBlockResultType
  elabNestedActions cond fun cond => do
  doElabToSyntax "debug_assert! body" (dec.continueWithUnit stx) fun body => do
  Term.elabTerm (← `(debug_assert! $cond; $body)) mγ
