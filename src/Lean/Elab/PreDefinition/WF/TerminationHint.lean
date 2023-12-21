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
  -- TODO: Why can I not just use $wf.vars in the quotation below?
  let vars : TSyntaxArray `ident := wf.vars.map (⟨·.raw⟩)
  if vars.isEmpty then
    `(terminationBy|termination_by $wf.body)
  else
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
  /-- Here we record the number of parameters past the `:`. This is currently
  only used by GuessLex when there is no `termination_by` annotation, so that
  we can print the guessed order in the right form.

  It it set in `TerminationHints.checkVars`, which is the place where we
  check that we have the right number of variables when there *is* a user-provided
  `termination_by`.
  -/
  extraParams : Nat
  deriving Inhabited

def TerminationHints.none : TerminationHints := ⟨.missing, .none, .none, 0⟩

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

/--
Checks that `termination_by` binds exactly as many variables are present in the outermost
lambda of `value`, and logs (without failing) appropriate errors.

Also remembers `extraParams`, so that we can later (in GuessLex) produce valid termination hints.
-/
def TerminationHints.checkVars (headerParams : Nat) (hints : TerminationHints) (value : Expr) :
    MetaM TerminationHints := do
  let extraParams := value.getNumHeadLambdas - headerParams
  if let .some tb := hints.termination_by? then
    if tb.vars.size != extraParams then
      if tb.vars.isEmpty then
        logErrorAt tb.ref <| m!"The function definition has {extraParams} extra parameters. " ++
          "These need to be bound here (`termination_by x1 ... xn =>`)."
      else if extraParams = 0 then
        logErrorAt tb.ref <| "The function definition has no extra parameters, so `termination_by` " ++
          "should not bind any. Variables bound in the function header can be referred directly."
      else
        logErrorAt tb.ref <| m!"The function definition has {extraParams} extra paramters, " ++
          m!"but {tb.vars.size} variables are bound here. Bind exactly {extraParams} variables here!"
  return { hints with extraParams := extraParams }


open Parser.Termination

/-- Takes apart a `Termination.suffix` syntax object -/
def elabTerminationHints {m} [Monad m] [MonadError m] (stx : TSyntax ``suffix) : m TerminationHints := do
  if let .missing := stx.raw then
    return { TerminationHints.none with ref := stx }
  if stx.raw.matchesNull 0 then
    return { TerminationHints.none with ref := stx }
  match stx with
  | `(suffix| $[$t?:terminationBy]? $[$d?:decreasingBy]? ) => do
    let termination_by? ← t?.mapM fun t => match t with
      | `(terminationBy|termination_by $vars* => $body) =>
        if vars.isEmpty then
          throwErrorAt t "no extra parameters bounds, please omit the `=>`"
        else
          pure {ref := t, vars, body}
      | `(terminationBy|termination_by $body:term) => pure {ref := t, vars := #[], body}
      | _ => throwErrorAt t "unexpected `termination_by` syntax"
    let decreasing_by? ← d?.mapM fun d => match d with
      | `(decreasingBy|decreasing_by $tactic) => pure {ref := d, tactic}
      | _ => throwErrorAt d "unexpected `decreasing_by` syntax"
    return { ref := stx, termination_by?, decreasing_by?, extraParams := 0 }
  | _ => throwErrorAt stx s!"Unexpected Termination.suffix syntax: {stx} of kind {stx.raw.getKind}"

end Lean.Elab.WF
