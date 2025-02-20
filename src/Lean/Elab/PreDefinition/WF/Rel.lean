/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Meta.Tactic.Apply
import Lean.Meta.Tactic.Cases
import Lean.Meta.Tactic.Rename
import Lean.Elab.SyntheticMVars
import Lean.Elab.PreDefinition.Basic
import Lean.Elab.PreDefinition.TerminationMeasure
import Lean.Meta.ArgsPacker

namespace Lean.Elab.WF
open Meta
open Term

/--
The termination measures must not depend on the varying parameters of the function, and in
a mutual clique, they must be the same for all functions.

This ensures the preconditions for `ArgsPacker.uncurryND`.
-/
def checkCodomains (names : Array Name) (prefixArgs : Array Expr) (arities : Array Nat)
    (termMeasures : TerminationMeasures) : TermElabM Expr := do
  let mut codomains := #[]
  for name in names, arity in arities, termMeasure in termMeasures do
    let type ← inferType (termMeasure.fn.beta prefixArgs)
    let codomain ← forallBoundedTelescope type arity fun xs codomain => do
      let fvars := xs.map (·.fvarId!)
      if codomain.hasAnyFVar (fvars.contains ·) then
        throwErrorAt termMeasure.ref  m!"The termination measure's type must not depend on the " ++
          m!"function's varying parameters, but {name}'s termination measure does:{indentExpr type}\n" ++
          "Try using `sizeOf` explicitly"
      pure codomain
    codomains := codomains.push codomain

  let codomain0 := codomains[0]!
  for h : i in [1 : codomains.size] do
    unless ← isDefEqGuarded codomain0 codomains[i] do
      throwErrorAt termMeasures[i]!.ref m!"The termination measures of mutually recursive functions " ++
        m!"must have the same return type, but the termination measure of {names[0]!} has type" ++
        m!"{indentExpr codomain0}\n" ++
        m!"while the termination measure of {names[i]!} has type{indentExpr codomains[i]}\n" ++
        "Try using `sizeOf` explicitly"
  return codomain0

/--
If the `termMeasures` map the packed argument `argType` to `β`, then this function passes to the
continuation a value of type `WellFoundedRelation argType` that is derived from the instance
for `WellFoundedRelation β` using `invImage`.
-/
def elabWFRel (declNames : Array Name) (unaryPreDefName : Name) (prefixArgs : Array Expr)
    (argsPacker : ArgsPacker) (argType : Expr) (termMeasures : TerminationMeasures)
    (k : Expr → TermElabM α) : TermElabM α := withDeclName unaryPreDefName do
  let α := argType
  let u ← getLevel α
  let β ← checkCodomains declNames prefixArgs argsPacker.arities termMeasures
  let v ← getLevel β
  let packedF ← argsPacker.uncurryND (termMeasures.map (·.fn.beta prefixArgs))
  let inst ← synthInstance (.app (.const ``WellFoundedRelation [v]) β)
  let rel ← instantiateMVars (mkApp4 (.const ``invImage [u,v]) α β packedF inst)
  k rel

end Lean.Elab.WF
