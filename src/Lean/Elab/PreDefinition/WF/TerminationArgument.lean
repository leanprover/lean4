/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Joachim Breitner
-/
prelude

import Lean.Parser.Term
import Lean.Elab.Term
import Lean.Elab.Binders
import Lean.Elab.SyntheticMVars
import Lean.Elab.PreDefinition.WF.TerminationHint
import Lean.PrettyPrinter.Delaborator

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
  let r ← withoutErrToSorry <|
    forallBoundedTelescope type (arity - extraParams) fun ys type' => do
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

open PrettyPrinter Delaborator SubExpr Parser.Termination Parser.Term in
def TerminationArgument.delab (termArg : TerminationArgument) : MetaM (TSyntax ``terminationBy) := do
  lambdaTelescope termArg.fn fun ys e => do
    let e ← mkLambdaFVars ys[termArg.arity - termArg.extraParams:] e -- undo overshooting by lambdaTelescope
    pure (← delabCore e (delab := go termArg.extraParams #[])).1
  where
    go : Nat → TSyntaxArray `ident → DelabM (TSyntax ``terminationBy)
    | 0, vars => do
      let stxBody ← Delaborator.delab
      let hole : TSyntax `Lean.Parser.Term.hole ← `(hole|_)

      -- any variable not mentioned syntatically (it may appear in the `Expr`, so do not just use
      -- `e.bindingBody!.hasLooseBVar`) should be delaborated as a hole.
      let vars  : TSyntaxArray [`ident, `Lean.Parser.Term.hole] :=
        Array.map (fun (i : Ident) => if hasIdent i.getId stxBody then i else hole) vars
      -- drop trailing underscores
      let mut vars := vars
      while ! vars.isEmpty && vars.back.raw.isOfKind ``hole do vars := vars.pop
      if vars.isEmpty then
        `(terminationBy|termination_by $stxBody)
      else
        `(terminationBy|termination_by $vars* => $stxBody)
    | i+1, vars => do
      let e ← getExpr
      unless e.isLambda do return ← go 0 vars -- should not happen
      withBindingBodyUnusedName fun n => go i (vars.push ⟨n⟩)
