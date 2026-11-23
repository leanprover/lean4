/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
public import Lean.Elab.PreDefinition.Basic
public import Lean.Elab.PreDefinition.Structural.Basic

public section

namespace Lean.Elab.Structural
open Meta

/-- Does `e` contain a matcher marked for reduction by smart unfolding? -/
private def containsSmartUnfoldingMatch (e : Expr) : Bool :=
  (e.find? fun e => (smartUnfoldingMatch? e).isSome).isSome

/-- Set bit `start + i` when `args[i]` contains a match that smart unfolding must reduce. -/
private def smartUnfoldingInputMask (start : Nat) (args : Array Expr) : Nat := Id.run do
  let mut mask := 0
  for h : i in *...args.size do
    if containsSmartUnfoldingMatch args[i] then
      mask := mask ||| (1 <<< (start + i))
  return mask

/--
Build `f._sunfold` by annotating the original body of `f`. Each entry in `recFns` gives the
name of a function in the mutual group and the position of its structural argument.
-/
partial def addSmartUnfoldingDefAux (preDef : PreDefinition) (recFns : Array (Name × Nat)) :
    MetaM PreDefinition := do
  return { preDef with
    declName  := mkSmartUnfoldingNameFor preDef.declName
    value     := (← visit preDef.value)
    modifiers := default
  }
where
  /--
  Mark a matcher application `e` with `markSmartUnfoldingMatch` if it contains a recursive call
  whose structural argument contains a loose bound variable. This is the `recArgHasLooseBVarsAt`
  test that `mkBRecOn` uses to decide whether to refine `below` at `e`.

  Visit the discriminants, alternative bodies, and extra arguments of a marked matcher. If an
  alternative body contains no marked matcher, mark it with `markSmartUnfoldingMatchAlt`. Once
  the reducer has checked the inputs and selected that alternative, it can return the body immediately.
  -/
  visit (e : Expr) : MetaM Expr := do
    match e with
    | Expr.lam ..     => lambdaTelescope e fun xs b => do mkLambdaFVars xs (← visit b)
    | Expr.forallE .. => goForall #[] e
    | Expr.letE ..    => goLet #[] e
    | Expr.mdata d b     => return mkMData d (← visit b)
    | Expr.proj n i s    => return mkProj n i (← visit s)
    | Expr.app .. =>
      let processApp (e : Expr) : MetaM Expr :=
        e.withApp fun f args =>
          return mkAppN (← visit f) (← args.mapM visit)
      match (← matchMatcherApp? e) with
      | some matcherApp =>
        if recFns.all fun (fnName, recArgPos) => !recArgHasLooseBVarsAt fnName recArgPos e then
          processApp e
        else
          let mut altsNew := #[]
          for alt in matcherApp.alts, numParams in matcherApp.altNumParams do
            let altNew ← lambdaBoundedTelescope alt numParams fun xs altBody => do
              unless xs.size = numParams do
                throwError "unexpected matcher application alternative{indentExpr alt}\nat application{indentExpr e}"
              let altBody ← visit altBody
              let altBody := if containsSmartUnfoldingMatch altBody then altBody else markSmartUnfoldingMatchAlt altBody
              mkLambdaFVars xs altBody
            altsNew := altsNew.push altNew
          let discrs ← matcherApp.discrs.mapM visit
          let remaining ← matcherApp.remaining.mapM visit
          -- In `match some (match n with ...) with | some x => x | none => ...`, the outer
          -- match can return `x` even when the marked match on `n` is stuck. The reducer must
          -- check that discriminant first. Likewise, a function-valued alternative can return
          -- an extra argument containing a stuck match. A zero mask skips both checks.
          let inputs := smartUnfoldingInputMask matcherApp.getFirstDiscrPos discrs |||
            smartUnfoldingInputMask matcherApp.arity remaining
          return markSmartUnfoldingMatch { matcherApp with alts := altsNew, discrs, remaining }.toExpr inputs
      | _ => processApp e
    | _ => return e

  /-- Accumulate the binders so each domain and the final body are instantiated only once. -/
  goForall (xs : Array Expr) (e : Expr) : MetaM Expr := do
    match e with
    | .forallE n d b bi =>
      withLocalDecl n bi (← visit (d.instantiateRev xs)) fun x =>
        goForall (xs.push x) b
    | _ => mkForallFVars xs (← visit (e.instantiateRev xs))

  /-- Visit consecutive `let` values in order and instantiate the body once for the whole block. -/
  goLet (xs : Array Expr) (e : Expr) : MetaM Expr := do
    match e with
    | .letE n t v b nondep =>
      let v ← visit (v.instantiateRev xs)
      withLetDecl n (t.instantiateRev xs) v (nondep := nondep) fun x =>
        goLet (xs.push x) b
    | _ => mkLetFVars xs (← visit (e.instantiateRev xs)) (generalizeNondepLet := false)

/-- Add `f._sunfold` to the environment for a structurally recursive definition `f`. Proofs are skipped. -/
partial def addSmartUnfoldingDef
    (docCtx : LocalContext × LocalInstances) (preDef : PreDefinition) (recFns : Array (Name × Nat)) :
    TermElabM Unit := do
  if (← isProp preDef.type) then
    return ()
  else
    withEnableInfoTree false do
      let preDefSUnfold ← addSmartUnfoldingDefAux preDef recFns
      -- `structuralRecursion` has already abstracted the nested proofs in `preDef.value`
      addNonRec docCtx preDefSUnfold (cleanupValue := true) (abstractProofs := false)

end Lean.Elab.Structural
