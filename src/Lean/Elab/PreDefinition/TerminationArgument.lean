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
import Lean.Elab.PreDefinition.TerminationHint
import Lean.PrettyPrinter.Delaborator.Basic

/-!
This module contains
* the data type `TerminationArgument`, the elaborated form of a `TerminationBy` clause,
* the `TerminationArguments` type for a clique, and
* elaboration and deelaboration functions.
-/

set_option autoImplicit false

namespace Lean.Elab

open Lean Meta Elab Term

/--
Elaborated form for a `termination_by` clause.

The `fn` has the same (value) arity as the recursive functions (stored in
`arity`), and maps its arguments (including fixed prefix, in unpacked form) to
the termination argument.

If `structural := Bool`, then the `fn` is a lambda picking out exactly one argument.
-/
structure TerminationArgument where
  ref : Syntax
  structural : Bool
  fn : Expr
deriving Inhabited

/-- A complete set of `TerminationArgument`s, as applicable to a single clique.  -/
abbrev TerminationArguments := Array TerminationArgument

/--
Elaborates a `TerminationBy` to an `TerminationArgument`.

* `type` is the full type of the original recursive function, including fixed prefix.
* `hint : TerminationBy` is the syntactic `TerminationBy`.
-/
def TerminationArgument.elab (funName : Name) (type : Expr) (arity extraParams : Nat)
    (hint : TerminationBy) : TermElabM TerminationArgument := withDeclName funName do
  assert! extraParams ≤ arity

  if h : hint.vars.size > extraParams then
    let mut msg := m!"{parameters hint.vars.size} bound in `termination_by`, but the body of " ++
      m!"{funName} only binds {parameters extraParams}."
    if let `($ident:ident) := hint.vars[0] then
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

        -- Structural recursion: The body has to be a single parameter, whose index we return
        if hint.structural then unless (ys ++ xs).contains body do
          let params := MessageData.andList ((ys ++ xs).toList.map (m!"'{·}'"))
          throwErrorAt hint.ref m!"The termination argument of a structurally recursive " ++
            m!"function must be one of the parameters {params}, but{indentExpr body}\nisn't " ++
            m!"one of these."

        -- Now abstract also over the remaining extra parameters
        forallBoundedTelescope type'.get! (extraParams - hint.vars.size) fun zs _ => do
          mkLambdaFVars (ys ++ xs ++ zs) body
  check r
  pure { ref := hint.ref, structural := hint.structural, fn := r}
  where
    parameters : Nat → MessageData
    | 1 => "one parameter"
    | n => m!"{n} parameters"

def TerminationArgument.structuralArg (termArg : TerminationArgument) : MetaM Nat := do
  assert! termArg.structural
  lambdaTelescope termArg.fn fun ys e => do
    let .some idx := ys.indexOf? e
      | panic! "TerminationArgument.structuralArg: body not one of the parameters"
    return idx


open PrettyPrinter Delaborator SubExpr Parser.Termination Parser.Term in
/--
Delaborates a `TerminationArgument` back to a `TerminationHint`, e.g. for `termination_by?`.

This needs extra information:
* `arity` is the value arity of the recursive function
* `extraParams` indicates how many of the functions arguments are bound “after the colon”.
-/
def TerminationArgument.delab (arity : Nat) (extraParams : Nat) (termArg : TerminationArgument) : MetaM (TSyntax ``terminationBy) := do
  lambdaBoundedTelescope termArg.fn (arity - extraParams) fun _ys e => do
    pure (← delabCore e (delab := go extraParams #[])).1
  where
    go : Nat → TSyntaxArray `ident → DelabM (TSyntax ``terminationBy)
    | 0, vars => do
      let stxBody ← Delaborator.delab
      let hole : TSyntax `Lean.Parser.Term.hole ← `(hole|_)

      -- any variable not mentioned syntactically (it may appear in the `Expr`, so do not just use
      -- `e.bindingBody!.hasLooseBVar`) should be delaborated as a hole.
      let vars  : TSyntaxArray [`ident, `Lean.Parser.Term.hole] :=
        Array.map (fun (i : Ident) => if stxBody.raw.hasIdent i.getId then i else hole) vars
      -- drop trailing underscores
      let mut vars := vars
      while ! vars.isEmpty && vars.back!.raw.isOfKind ``hole do vars := vars.pop
      if termArg.structural then
        if vars.isEmpty then
          `(terminationBy|termination_by structural $stxBody)
        else
          `(terminationBy|termination_by structural $vars* => $stxBody)
      else
        if vars.isEmpty then
          `(terminationBy|termination_by $stxBody)
        else
          `(terminationBy|termination_by $vars* => $stxBody)
    | i+1, vars => do
      let e ← getExpr
      unless e.isLambda do return ← go 0 vars -- should not happen
      withBindingBodyUnusedName fun n => go i (vars.push ⟨n⟩)

end Lean.Elab
