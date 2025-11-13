/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
module

prelude
public import Lean.Elab.Do.Basic
meta import Lean.Parser.Do
import Lean.Meta.ProdN
import Lean.Elab.Do.Control

public section

namespace Lean.Elab.Do

open Lean Parser Meta Elab Do

@[builtin_doElem_elab Lean.Parser.Do.doReturn] def elabDoReturn : DoElab := fun stx _dec => do
  let `(doReturn| return $e) := stx | throwUnsupportedSyntax
  let returnCont ← getReturnCont
  let e ← elabTermEnsuringType e returnCont.resultType
  mapLetDeclZeta returnCont.resultName returnCont.resultType e fun _ =>
    returnCont.k

@[builtin_doElem_elab Lean.Parser.Do.doBreak] def elabDoBreak : DoElab := fun _stx _dec => do
  let some breakCont := (← getBreakCont)
    | throwError "`break` must be nested inside a loop"
  breakCont

@[builtin_doElem_elab Lean.Parser.Do.doContinue] def elabDoContinue : DoElab := fun _stx _dec => do
  let some continueCont := (← getContinueCont)
    | throwError "`continue` must be nested inside a loop"
  continueCont

@[builtin_doElem_elab Lean.Parser.Do.doExpr] def elabDoExpr : DoElab := fun stx dec => do
  let `(doExpr| $e:term) := stx | throwUnsupportedSyntax
  let mα ← mkMonadicType dec.resultType
  let e ← elabTermEnsuringType e mα
  dec.mkBindUnlessPure e

@[builtin_doElem_elab Lean.Parser.Do.doNested] def elabDoNested : DoElab := fun stx dec => do
  let `(doNested| do $doSeq) := stx | throwUnsupportedSyntax
  elabDoSeq ⟨doSeq.raw⟩ dec

@[builtin_doElem_elab Lean.Parser.Do.doLet] def elabDoLet : DoElab := fun stx dec => do
  let `(doLet| let $[mut%$mutTk?]? $x:ident $[: $xType?]? := $rhs) := stx | throwUnsupportedSyntax
  checkMutVarsForShadowing x.getId
  -- We want to allow `do let foo : Nat = Nat := rfl; pure (foo ▸ 23)`. Note that the type of
  -- foo has sort `Sort 0`, whereas the sort of the monadic result type `Nat` is `Sort 1`.
  -- Hence `freshLevel := true` (yes, even for `mut` vars; why not?).
  let xType ← elabType xType? (freshLevel := true)
  let rhs ← elabTermEnsuringType rhs xType
  mapLetDecl (usedLetOnly := false) x.getId xType rhs fun _xdefn => declareMutVar? mutTk? x.getId dec.continueWithUnit

@[builtin_doElem_elab Lean.Parser.Do.doLetArrow] def elabDoLetArrow : DoElab := fun stx dec => do
  let `(doLetArrow| let $[mut%$mutTk?]? $x:ident $[: $xType?]? ← $rhs) := stx | throwUnsupportedSyntax
  checkMutVarsForShadowing x.getId
  let xType ← elabType xType?
  let lctx ← getLCtx
  let mutVars := (← read).mutVars
  elabDoElem rhs <| .mk x.getId xType do
    withLCtxKeepingMutVarDefs lctx mutVars x.getId do
      declareMutVar? mutTk? x.getId dec.continueWithUnit

@[builtin_doElem_elab Lean.Parser.Do.doReassignArrow] def elabDoReassignArrow : DoElab := fun stx dec => do
  let `(doReassignArrow| $x:ident ← $rhs) := stx | throwUnsupportedSyntax
  throwUnlessMutVarDeclared x.getId
  let xType := (← getLocalDeclFromUserName x.getId).type
  let lctx ← getLCtx
  let mutVars := (← read).mutVars
  elabDoElem rhs <| .mk x.getId xType do
    withLCtxKeepingMutVarDefs lctx mutVars x.getId do
      dec.continueWithUnit

@[builtin_doElem_elab Lean.Parser.Do.doReassign] def elabDoReassign : DoElab := fun stx dec => do
  let `(doReassign| $x:ident := $rhs) := stx | throwUnsupportedSyntax
  throwUnlessMutVarDeclared x.getId
  let xType := (← getLocalDeclFromUserName x.getId).type
  let rhs ← elabTermEnsuringType rhs xType
  mapLetDecl (usedLetOnly := false) x.getId xType rhs fun _xdefn => dec.continueWithUnit

@[builtin_doElem_elab Lean.Parser.Do.doLetElse] def elabDoLetElse : DoElab := fun _ _ => do
  throwError "Not implemented yet"

def elabDoIf : DoElab := fun stx dec => do
  let `(doElem| if $cond then $thenDooSeq $[else $elseDooSeq?]?) := stx | throwUnsupportedSyntax
  dec.withDuplicableCont fun dec => do
    let then_ ← elabDoSeq ⟨thenDooSeq.raw⟩ dec
    let else_ ← match elseDooSeq? with
      | none => dec.continueWithUnit
      | some elseDooSeq => elabDoSeq ⟨elseDooSeq.raw⟩ dec
    let then_ ← Term.exprToSyntax then_
    let else_ ← Term.exprToSyntax else_
    elabTerm (← `(if $cond then $then_ else $else_)) none

@[builtin_doElem_elab Lean.Parser.Do.doFor] def elabDoFor : DoElab := fun stx dec => do
  let `(doFor| for $x:ident in $xs do $doSeq) := stx | throwUnsupportedSyntax
  let uα ← mkFreshLevelMVar
  let uρ ← mkFreshLevelMVar
  let α ← mkFreshExprMVar (mkSort (mkLevelSucc uα)) (userName := `α)
  let ρ ← mkFreshExprMVar (mkSort (mkLevelSucc uρ)) (userName := `ρ)
  let xs ← elabTermEnsuringType xs ρ
  let mi := (← read).monadInfo
  let σ ← mkFreshExprMVar (mkSort (mkLevelSucc mi.u)) (userName := `σ)
  let γ := (← read).doBlockResultType
  let β ← mkArrow σ (← mkMonadicType γ)
  let mutVars := (← read).mutVars
  let breakRhs ← mkFreshExprMVar β
  withLetDecl (← mkFreshUserName `kbreak) β breakRhs (kind := .implDetail) (nondep := true) fun kbreak => do
  withLocalDeclD x.getId α fun x => do
  withLocalDecl (← mkFreshUserName `kcontinue) .default β (kind := .implDetail) fun kcontinue => do
  withLocalDecl (← mkFreshUserName `s) .default σ (kind := .implDetail) fun loopS => do
  withProxyMutVarDefs fun elimProxyDefs => do
    let rootCtx ← getLCtx
    let continueKVar ← mkFreshContVar γ mutVars
    let breakKVar ← mkFreshContVar γ mutVars

    -- Elaborate the loop body, which must have result type `PUnit`.
    let body ← enterLoopBody γ (← getReturnCont) breakKVar.mkJump continueKVar.mkJump do
      elabDoSeq doSeq { dec with k := continueKVar.mkJump }

    -- Compute the set of mut vars that were reassigned on the path to a back jump (`continue`).
    -- Take care to preserve the declaration order that is manifest in the array `mutVars`.
    let loopMutVars ← do
      let ctn ← continueKVar.getReassignedMutVars rootCtx
      let brk ← breakKVar.getReassignedMutVars rootCtx
      pure (ctn.union brk)
    let loopMutVars := mutVars.filter loopMutVars.contains

    -- Assign the state tuple type and the initial tuple of states.
    let preS ← σ.mvarId!.withContext do
      let defs ← loopMutVars.mapM (getFVarFromUserName ·)
      let (tuple, tupleTy) ← mkProdMkN defs
      synthUsingDefEq "state tuple type" σ tupleTy
      pure tuple

    -- Synthesize the `continue` and `break` jumps.
    continueKVar.synthesizeJumps do
      let (tuple, _tupleTy) ← mkProdMkN (← loopMutVars.mapM (getFVarFromUserName ·))
      return mkApp kcontinue tuple
    breakKVar.synthesizeJumps do
      let (tuple, _tupleTy) ← mkProdMkN (← loopMutVars.mapM (getFVarFromUserName ·))
      return mkApp kbreak tuple

    -- Elaborate the continuation, now that `σ` is known. It will be the `break` handler.
    -- If there is a `break`, the code will be shared in the `kbread` join point.
    breakRhs.mvarId!.withContext do
      let e ← withLocalDeclD (← mkFreshUserName `s) σ fun postS => do mkLambdaFVars #[postS] <| ← do
        bindMutVarsFromTuple loopMutVars.toList postS.fvarId! do
          dec.continueWithUnit
      synthUsingDefEq "break RHS" breakRhs e

    -- Finally eliminate the proxy variables from the loop body.
    -- * Point non-reassigned mut var defs to the pre state
    -- * Point the initial defs of reassigned mut vars to the loop state
    -- Done by `elimProxyDefs` below.
    let body ← bindMutVarsFromTuple loopMutVars.toList loopS.fvarId! do
      elimProxyDefs body

    let hadBreak := (← breakKVar.jumpCount) > 0
    let kcons ← mkLambdaFVars #[x, kcontinue, loopS] body
    let knil := if hadBreak then kbreak else breakRhs
    let instForIn ← Term.mkInstMVar <| mkApp3 (mkConst ``ForInNew [uρ, uα, mi.u, mi.v]) mi.m ρ α
    let app := mkConst ``ForInNew.forIn [uρ, uα, mi.u, mi.v]
    let app := mkApp10 app mi.m ρ α instForIn σ γ xs preS kcons knil
    if hadBreak then
      mkLetFVars (generalizeNondepLet := false) #[kbreak] app
    else
      return (← elimMVarDeps #[kbreak] app).replaceFVar kbreak breakRhs

@[builtin_doElem_elab Lean.Parser.Do.doTry] def elabDoTry : DoElab := fun stx dec => do
  let `(doTry| try $trySeq:doSeq $[catch $xs $[: $eTypes?]? => $catchSeqs]* $[finally $finSeq?]?) := stx | throwUnsupportedSyntax
  for x in xs do if x.raw.isIdent then
    checkMutVarsForShadowing x.raw.getId
  if catchSeqs.isEmpty && finSeq?.isNone then
    throwError "Invalid `try`. There must be a `catch` or `finally`."
  -- We cannot use join points because `tryCatch` and `tryFinally` are never tail-resumptive.
  -- (Proof: `do tryCatch e h; throw x ≠ tryCatch (do e; throw x) (fun e => do h e; throw x)`)
  -- This is also known as the "algebraicity property" in the algebraic effects and handlers
  -- community.
  --
  -- So we need to pack up our effects and unpack them after the `try`.
  -- We could optimize for the `.last` case by omitting the state tuple ... in the future.
  let mi := (← read).monadInfo
  let lifter ← Lean.Elab.Do.ControlLifter.ofCont dec
  let body ← lifter.lift (elabDoSeq trySeq)
  let body ← xs.zip (eTypes?.zip catchSeqs) |>.foldlM (init := body) fun body (x, eType?, catchSeq) => do
    let x := Term.mkExplicitBinder x.raw <| match eType? with
      | some eType => eType
      | none => mkHole x
    let (catch_, ε, uε) ← elabBinder x fun x => do
      let ε ← inferType x
      let uε ← getDecLevel ε
      let catch_ ← lifter.lift (elabDoSeq catchSeq)
      let catch_ ← mkLambdaFVars #[x] catch_
      return (catch_, ε, uε)
    if eType?.isSome then
      let inst ← Term.mkInstMVar <| mkApp2 (mkConst ``MonadExceptOf [uε, mi.u, mi.v]) ε mi.m
      return mkApp6 (mkConst ``tryCatchThe [uε, mi.u, mi.v])
        ε mi.m inst lifter.resultType body catch_
    else
      let inst ← Term.mkInstMVar <| mkApp2 (mkConst ``MonadExcept [uε, mi.u, mi.v]) ε mi.m
      return mkApp6 (mkConst ``MonadExcept.tryCatch [uε, mi.u, mi.v])
        ε mi.m inst lifter.resultType body catch_
  let body ← match finSeq? with
    | none => pure body
    | some finSeq => do
      let β ← mkFreshResultType `β
      let fin ← enterFinally β <| elabDoSeq finSeq (← DoElemCont.mkPure β)
      let instMonadFinally ← Term.mkInstMVar <| mkApp (mkConst ``MonadFinally [mi.u, mi.v]) mi.m
      let instFunctor ← Term.mkInstMVar <| mkApp (mkConst ``Functor [mi.u, mi.v]) mi.m
      pure <| mkApp7 (mkConst ``tryFinally [mi.u, mi.v])
        mi.m lifter.resultType β instMonadFinally instFunctor body fin
  (← lifter.restoreCont).mkBindUnlessPure body
