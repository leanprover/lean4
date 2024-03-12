/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Joachim Breitner
-/
prelude

import Lean.Parser.Term
import Lean.Elab.Term
import Lean.Elab.Binders
import Lean.Elab.SyntheticMVars
import Lean.Elab.PreDefinition.WF.TerminationHint
import Lean.PrettyPrinter.Delaborator.Basic

/-!
This module contains the data type `TerminationArgument`, the elaborated form of a `TerminationBy`
clause, the `TerminationArguments` type for a clique and the elaboration functions.
-/

set_option autoImplicit false

namespace Lean.Elab.WF

open Lean Meta Elab Term

/--
Elaborated form for a `termination_by` clause.

The `fn` has the same (value) arity as the recursive functions (stored in
`arity`), and maps its arguments (including fixed prefix, in unpacked form) to
the termination argument.
-/
structure TerminationArgument where
  ref : Syntax
  arity : Nat
  extraParams : Nat
  fn : Expr
deriving Inhabited

/-- A complete set of `TerminationArgument`s, as applicable to a single clique.  -/
abbrev TerminationArguments := Array TerminationArgument

/--
Elaborates a `TerminationBy` to an `TerminationArgument`.

* `type` is the full type of the original recursive function, including fixed prefix.
* `arity` is the value arity of the recursive function; the termination argument cannot take more.
* `extraParams` is the the number of parameters the function has after the colon; together with
  `arity` indicates how many parameters of the function are before the colon and thus in scope.
* `hint : TerminationBy` is the syntactic `TerminationBy`.
-/
def TerminationArgument.elab (funName : Name) (type : Expr) (arity extraParams : Nat)
    (hint : TerminationBy) : TermElabM TerminationArgument := withDeclName funName do
  assert! extraParams ≤ arity

  if hint.vars.size > extraParams then
    let mut msg := m!"{parameters hint.vars.size} bound in `termination_by`, but the body of " ++
      m!"{funName} only binds {parameters extraParams}."
    if let `($ident:ident) := hint.vars[0]! then
      if ident.getId.isSuffixOf funName then
          msg := msg ++ m!" (Since Lean v4.6.0, the `termination_by` clause no longer " ++
            "expects the function name here.)"
    throwErrorAt hint.ref msg

  -- Bring parameters before the colon into scope
  let r ← forallBoundedTelescope type (arity - extraParams) fun ys type' => do
    -- Bring the variables bound by `termination_by` into scope.
    elabFunBinders hint.vars (some type') fun xs type' => do
      -- Elaborate the body in this local environment
      let body ← Lean.Elab.Term.withSynthesize <| elabTermEnsuringType hint.body none
      -- Now abstract also over the remaining extra parameters
      forallBoundedTelescope type'.get! (extraParams - hint.vars.size) fun zs _ => do
        mkLambdaFVars (ys ++ xs ++ zs) body
  -- logInfo m!"elabTermValue: {r}"
  check r
  pure { ref := hint.ref, arity, extraParams, fn := r}
  where
    parameters : Nat → MessageData
    | 1 => "one parameter"
    | n => m!"{n} parameters"

open Parser.Termination in
open Parser.Term in
def TerminationArgument.delab (termArg : TerminationArgument) : MetaM (TSyntax ``terminationBy) := do
  lambdaTelescope termArg.fn fun ys e => do
    let e ← mkLambdaFVars ys[termArg.arity - termArg.extraParams:] e -- undo overshooting by lambdaTelescope
    let stx ← PrettyPrinter.delab e -- this is a bit of a hack: We delaborate and then translate the syntax
    match stx with
    | `(fun $vars:funBinder* => $body) =>
      -- TODO: Take prefix
      let vars := vars.map (fun s => TSyntax.mk s)
      `(terminationBy|termination_by $vars* => $body)
    | _ => `(terminationBy|termination_by $stx)
