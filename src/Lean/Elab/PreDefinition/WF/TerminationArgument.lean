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

/-!
This module contains the data type `TerminationArgument`, the elaborated form of a `TerminationBy`
clause, the `TerminationArguments` type for a clique and the elaboration functions.
-/

set_option autoImplicit false

namespace Lean.Elab.WF

open Lean Meta Elab Term

/--
Elaborated form for a `termination_by` clause.

The `fn` maps a prefix of length `arity` of the recursive function's parameter to
the termination argument.
-/
structure TerminationArgument where
  arity : Nat
  fn : Expr


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
    (hint : TerminationBy) : TermElabM TerminationArgument := do
  assert! extraParams ≤ arity

  if hint.vars.size > extraParams then
    let mut msg := m!"{parameters hint.vars.size} bound in `termination_by`, but the body of " ++
      m!"{funName} only binds {parameters extraParams}."
    if let `($ident:ident) := hint.vars[0]! then
      if ident.getId.isSuffixOf funName then
          msg := msg ++ m!" (Since Lean v4.6.0, the `termination_by` clause no longer " ++
            "expects the function name here.)"
    throwErrorAt hint.ref msg

  if hint.vars.size > extraParams then
        throwError "termination argument binds too many variables, function value takes only {extraParams} parameters"
  let r ← forallBoundedTelescope type (arity - extraParams) fun ys type' => do
    -- The fixed prefix is in scope
    elabFunBinders hint.vars type' fun xs _ => do
      mkForallFVars (ys ++ xs) (← Lean.Elab.Term.withSynthesize <| elabTermEnsuringType hint.body none)
  check r
  logInfo m!"elabTermValue: {r}"
  pure { fn := r, arity := arity - extraParams + hint.vars.size}
  where
    parameters : Nat → MessageData
    | 1 => "one parameter"
    | n => m!"{n} parameters"
