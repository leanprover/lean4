/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner
-/
import Lean.Elab.ElabRules
import Lean.Meta.Closure
import Lean.Compiler.ImplementedByAttr

/-!
Defines term syntax to call unsafe functions.

```
def cool :=
  unsafe (unsafeCast () : Nat)

#eval cool
```
-/

namespace Lean.TermUnsafe

open Lean Meta Elab Term

/-- Construct an auxiliary name based on the current declaration name and the given `hint` base. -/
-- Note we already have `Lean.Elab.Term.mkAuxName` and `Lean.mkAuxName`.
-- This is slightly different again (doesn't fail it `getDeclName?` is empty,
-- and incorporates the macro scope into the generated name).
private def mkAuxName (hint : Name) : TermElabM Name :=
  withFreshMacroScope do
    let name := (← getDeclName?).getD Name.anonymous ++ hint
    pure $ addMacroScope (← getMainModule) name (← getCurrMacroScope)

@[builtin_term_elab «unsafe»]
def elabUnsafe : TermElab := fun stx expectedType? =>
  match stx with
  | `(unsafe $t) => do
    let mut t ← elabTerm t expectedType?
    t ← instantiateMVars t
    if t.hasExprMVar then
      synthesizeSyntheticMVarsNoPostponing
      t ← instantiateMVars t
    if ← logUnassignedUsingErrorInfos (← getMVars t) then throwAbortTerm
    t ← mkAuxDefinitionFor (← mkAuxName `unsafe) t
    let Expr.const unsafeFn unsafeLvls .. := t.getAppFn | unreachable!
    let ConstantInfo.defnInfo unsafeDefn ← getConstInfo unsafeFn | unreachable!
    let implName ← mkAuxName `impl
    addDecl <| Declaration.defnDecl {
      name := implName
      type := unsafeDefn.type
      levelParams := unsafeDefn.levelParams
      value := ← mkOfNonempty unsafeDefn.type
      hints := ReducibilityHints.opaque
      safety := DefinitionSafety.safe
    }
    setImplementedBy implName unsafeFn
    pure $ mkAppN (mkConst implName unsafeLvls) t.getAppArgs
  | _ => throwUnsupportedSyntax
