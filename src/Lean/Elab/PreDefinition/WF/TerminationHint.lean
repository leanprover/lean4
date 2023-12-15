/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Joachim Breitner
-/
import Lean.Parser.Term

set_option autoImplicit false

namespace Lean.Elab.WF

/-! # Support for `termination_by` notation -/

/-- A single `termination_by` clause -/
structure TerminationBy where
  ref       : Syntax
  vars      : TSyntaxArray [`ident, ``Lean.Parser.Term.hole]
  body      : Term
  deriving Inhabited

open Parser.Termination in
def TerminationBy.unexpand (wf : TerminationBy) : MetaM Syntax := do
  -- TODO: Why can I not use $wf.vars below?
  let vars : TSyntaxArray `ident := wf.vars.map (⟨·.raw⟩)
  `(terminationBy|termination_by $vars* => $wf.body)

/-- A complete set of `termination_by` hints, as applicable to a single clique.  -/
abbrev TerminationWF := Array TerminationBy

/-- A single `decreasing_by` clause -/
structure DecreasingBy where
  ref       : Syntax
  tactic    : TSyntax ``Lean.Parser.Tactic.tacticSeq
  deriving Inhabited

/-- The termination annotations for a single function.
For `decreasing_by`, we store the whole `decreasing_by tacticSeq` expression, as this
is what `Term.runTactic` expects.
 -/
structure TerminationHints where
  ref : Syntax
  termination_by? : Option TerminationBy
  decreasing_by?  : Option DecreasingBy
  deriving Inhabited

def TerminationHints.none : TerminationHints := ⟨.missing, .none, .none⟩

/-- Logs warnings when the `TerminationHints` are present.  -/
def TerminationHints.ensureNone (hints : TerminationHints) (reason : String): CoreM Unit := do
  match hints.termination_by?, hints.decreasing_by? with
  | .none, .none => pure ()
  | .none, .some dec_by =>
    logErrorAt dec_by.ref m!"unused `decreasing_by`, function is {reason}"
  | .some term_by, .none =>
    logErrorAt term_by.ref m!"unused `termination_by`, function is {reason}"
  | .some _, .some _ =>
    logErrorAt hints.ref m!"unused termination hints, function is {reason}"

open Parser.Termination

def elabTerminationHints (stx : TSyntax ``suffix) : TerminationHints :=
  -- TODO: Better understand if this is needed
  if let .missing := stx.raw then { TerminationHints.none with ref := stx }
  -- and why this is needed
  else if stx.raw.matchesNull 0 then { TerminationHints.none with ref := stx }
  else
    match stx with
  | `(suffix| $[$t?:terminationBy]? $[$d?:decreasingBy]? ) =>
    { ref := stx
      termination_by? := t?.map fun t => match t with
        | `(terminationBy|termination_by $vars* => $body) => {ref := t, vars, body}
        | _ => unreachable!
      decreasing_by? := d?.map fun t => match t with
        | `(decreasingBy|decreasing_by $tactic) => {ref := t, tactic}
        | _ => unreachable! }
  | _ => panic! s!"Unexpected Termination.suffix syntax: {stx} of kind {stx.raw.getKind}"

end Lean.Elab.WF
