/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
module

prelude
public import Lean.Elab.BuiltinDo.Basic
meta import Lean.Parser.Do
import Lean.Meta.ProdN

public section

namespace Lean.Elab.Do

open Lean.Parser.Term
open Lean.Meta

@[builtin_macro Lean.Parser.Term.doFor] def expandDoFor : Macro := fun stx => do
  match stx with
  | `(doFor| for $[$_ : ]? $_:ident in $_ do $_) =>
    -- This is the target form of the expander, handled by `elabDoFor` below.
    Macro.throwUnsupported
  | `(doFor| for $decls:doForDecl,* do $body) =>
    let decls := decls.getElems
    let `(doForDecl| $[$h? : ]? $pattern in $xs) := decls[0]! | Macro.throwUnsupported
    let mut doElems := #[]
    let mut body := body
    -- Expand `pattern` into an `Ident` `x`:
    let x ←
      if pattern.raw.isIdent then
        pure ⟨pattern⟩
      else
        let x ← Term.mkFreshIdent pattern
        body ← `(doSeq| match (generalizing := false) $x:term with | $pattern => $body)
        pure x
    -- Expand the remaining `doForDecl`s:
    for doForDecl in decls[1...*] do
      /-
        Expand
        ```
        for x in xs, y in ys do
          body
        ```
        into
        ```
        let mut s := Std.toStream ys
        for x in xs do
          match Std.Stream.next? s with
          | none => break
          | some (y, s') =>
            s := s'
            body
        ```
      -/
      let `(doForDecl| $[$h? : ]? $y in $ys) := doForDecl | Macro.throwUnsupported
      if let some h := h? then
        Macro.throwErrorAt h "The proof annotation here has not been implemented yet."
      /- Recall that `@` (explicit) disables `coeAtOutParam`.
         We used `@` at `Stream` functions to make sure `resultIsOutParamSupport` is not used. -/
      let toStreamApp ← withRef ys `(@Std.toStream _ _ _ $ys)
      let s := mkIdentFrom ys (← withFreshMacroScope <| MonadQuotation.addMacroScope `s)
      doElems := doElems.push (← `(doSeqItem| let mut $s := $toStreamApp:term))
      body ← `(doSeq|
        match @Std.Stream.next? _ _ _ $s with
          | none => break
          | some ($y, s') =>
            $s:ident := s'
            do $body)
    doElems := doElems.push (← `(doSeqItem| for $[$h? : ]? $x:ident in $xs do $body))
    `(doElem| do $doElems*)
  | _ => Macro.throwUnsupported

@[builtin_doElem_elab Lean.Parser.Term.doFor] def elabDoFor : DoElab := fun stx dec => do
  let `(doFor| for $[$h? : ]? $x:ident in $xs do $body) := stx | throwUnsupportedSyntax
  checkMutVarsForShadowing #[x]
  let uα ← mkFreshLevelMVar
  let uρ ← mkFreshLevelMVar
  let α ← mkFreshExprMVar (mkSort (mkLevelSucc uα)) (userName := `α) -- assigned by outParam
  let ρ ← mkFreshExprMVar (mkSort (mkLevelSucc uρ)) (userName := `ρ) -- assigned in the next line
  let xs ← Term.elabTermEnsuringType xs ρ
  let mi := (← read).monadInfo
  let mutVars := (← read).mutVars
  let mutVarNames := mutVars.map (·.getId)
  -- TODO: Refine set of loop mut vars
  -- Compute the set of mut vars that were reassigned on the path to a back jump (`continue`).
  -- Take care to preserve the declaration order that is manifest in the array `mutVars`.
  let loopMutVars := mutVars
  let loopMutVarNames := loopMutVars.map (·.getId) |>.toList
  let useLoopMutVars : TermElabM (Array Expr) := do
    let mut defs := #[]
    for x in loopMutVars do
      let defn ← getLocalDeclFromUserName x.getId
      Term.addTermInfo' x defn.toExpr
      -- ForInNew forces all mut vars into the same universe: that of the do block result type.
      discard <| Term.ensureHasType (mkSort (mkLevelSucc mi.u)) defn.type
      defs := defs.push defn.toExpr
    return defs

  unless ← isDefEq dec.resultType (← mkPUnit) do
    logError m!"Type mismatch. `for` loops have result type {← mkPUnit}, but the rest of the `do` sequence expected {dec.resultType}."

  let (preS, σ) ← mkProdMkN (← useLoopMutVars) mi.u

  let γ := (← read).doBlockResultType
  let β ← mkArrow σ (← mkMonadicType γ)
  let (app, p?) ← match h? with
    | none =>
      let instForIn ← Term.mkInstMVar <| mkApp3 (mkConst ``ForInNew [uρ, uα, mi.u, mi.v]) mi.m ρ α
      let app := mkConst ``ForInNew.forInNew [uρ, uα, mi.u, mi.v]
      let app := mkApp7 app mi.m ρ α instForIn σ γ xs -- 3 args remaining: preS, kcons, knil
      pure (app, none)
    | some _ =>
      let p ← mkFreshExprMVar (← mkArrowN #[ρ, α] (mkSort .zero)) (userName := `p) -- outParam
      let instForIn ← Term.mkInstMVar <| mkApp4 (mkConst ``ForInNew' [uρ, uα, mi.u, mi.v]) mi.m ρ α p
      let app := mkConst ``ForInNew'.forInNew' [uρ, uα, mi.u, mi.v]
      let app := mkApp8 app mi.m ρ α p instForIn σ γ xs -- 3 args remaining: preS, kcons, knil
      pure (app, some p)
  let s ← mkFreshUserName `__s
  let kbreakName ← mkFreshUserName `__kbreak
  let kcontinueName ← mkFreshUserName `__kcontinue
  let breakRhsMVar ← mkFreshExprSyntheticOpaqueMVar β
  withLetDecl kbreakName β breakRhsMVar (kind := .implDetail) (nondep := true) fun kbreak => do
  withContFVar kbreakName do
  let xh : Array (Name × (Array Expr → DoElabM Expr)) := match h?, p? with
    | some h, some p => #[(x.getId, fun _ => pure α), (h.getId, fun x => pure (mkApp2 p xs x[0]!))]
    | _, _ => #[(x.getId, fun _ => pure α)]
  withLocalDeclsD xh fun xh => do
  withLocalDecl kcontinueName .default β (kind := .implDetail) fun kcontinue => do
  withContFVar kcontinueName do
  withLocalDecl s .default σ (kind := .implDetail) fun loopS => do
  -- withProxyMutVarDefs fun elimProxyDefs => do
    let continueCont := do
      let (tuple, _tupleTy) ← mkProdMkN (← useLoopMutVars) mi.u
      return mkApp kcontinue tuple
    -- let break? ← IO.mkRef false
    let breakCont := do
      -- break?.set true
      let (tuple, _tupleTy) ← mkProdMkN (← useLoopMutVars) mi.u
      return mkApp kbreak tuple

    -- Elaborate the loop body, which must have result type `PUnit`.
    let body ←
      enterLoopBody breakCont continueCont do
      bindMutVarsFromTuple loopMutVarNames loopS.fvarId! do
      elabDoSeq body { dec with k := continueCont, kind := .duplicable }

    -- Elaborate the `break` continuation.
    -- If there is a `break`, the code will be shared in the `kbreak` join point.
    -- We elaborate the continuation before the body so that type info from the continuation may
    -- flow into the loop body.
    let breakRhs ← breakRhsMVar.mvarId!.withContext do
      withLocalDeclD s σ fun postS => do mkLambdaFVars #[postS] <| ← do
        bindMutVarsFromTuple loopMutVarNames postS.fvarId! do
          dec.continueWithUnit
    unless ← breakRhsMVar.mvarId!.checkedAssign breakRhs do
      throwError "Failed to assign break continuation"

    let needBreakJoin := dec.kind matches .nonDuplicable -- && (← break?.get)
    let kcons ← mkLambdaFVars (xh ++ #[kcontinue, loopS]) body
    let knil := if needBreakJoin then kbreak else breakRhs
    let app := mkApp3 app preS kcons knil
    if needBreakJoin then
      mkLetFVars (generalizeNondepLet := false) #[kbreak] app
    else
      inlineJoinPointM app kbreak
