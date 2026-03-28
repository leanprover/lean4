import Lean

open Lean Meta

/-!
Test for sharing in `instantiateMVars` with delayed mvar assignments.

We construct the metavariable assignment graph for the goal
`∀ s, (s = s → (s = s) ∧ (s = s)) ∧ (s = s)`:

  ?root    :=  fun (s : Nat) => ?rootAux #0
  ?rootAux delayed [s_fvar] := ?body
  ?body    :=  @And.intro leftTy rightTy ?left right
  ?left    :=  fun (h : eq_ss) => ?leftAux #0
  ?leftAux delayed [h_fvar] := ?inner
  ?inner   :=  @And.intro eq_ss eq_ss h_fvar h_fvar

where

  eq_ss   := @Eq Nat s_fvar s_fvar            ← single shared object
  andTy   := And eq_ss eq_ss                  ← contains eq_ss
  leftTy  := eq_ss → andTy                    ← forallE body contains eq_ss
  rightTy := eq_ss
  right   := @Eq.refl Nat s_fvar

After instantiation, the shared `eq_ss` input should produce shared results
at each binding depth:
- At depth 1: `@Eq Nat #0 #0` (used as rightTy, leftTy.domain, left.domain)
- At depth 2: `@Eq Nat #1 #1` (used as And args in leftTy body and And.intro
  type args in inner body)
-/

private def mkTestRoot : MetaM Expr := do
  let nat := mkConst ``Nat
  withLocalDeclD `s nat fun s_fvar => do
    let eq_ss ← mkEq s_fvar s_fvar            -- shared object

    let andTy := mkApp2 (mkConst ``And) eq_ss eq_ss  -- (s=s) ∧ (s=s)
    let leftTy ← mkArrow eq_ss andTy          -- s=s → (s=s) ∧ (s=s)
    let rightTy := eq_ss                       -- s=s
    let bodyTy := mkApp2 (mkConst ``And) leftTy rightTy

    let body ← mkFreshExprMVar bodyTy
    let left ← mkFreshExprMVar leftTy

    withLocalDeclD `h eq_ss fun h_fvar => do
      -- ?inner : (s=s) ∧ (s=s), proved by And.intro eq_ss eq_ss h h
      let inner ← mkFreshExprMVar andTy
      let leftDecl ← left.mvarId!.getDecl
      let leftAux ← mkFreshExprMVarAt leftDecl.lctx leftDecl.localInstances
                       leftDecl.type .syntheticOpaque
      assignDelayedMVar leftAux.mvarId! #[h_fvar] inner.mvarId!
      left.mvarId!.assign (Lean.mkLambda `h .default eq_ss (mkApp leftAux (.bvar 0)))
      inner.mvarId!.assign (mkApp4 (mkConst ``And.intro) eq_ss eq_ss h_fvar h_fvar)

      let right := mkApp2 (mkConst ``Eq.refl [1]) nat s_fvar
      body.mvarId!.assign (mkApp4 (mkConst ``And.intro) leftTy rightTy left right)

      let rootTy ← mkForallFVars #[s_fvar] bodyTy
      let root ← mkFreshExprMVar rootTy
      let rootDecl ← root.mvarId!.getDecl
      let rootAux ← mkFreshExprMVarAt rootDecl.lctx rootDecl.localInstances
                       rootDecl.type .syntheticOpaque
      assignDelayedMVar rootAux.mvarId! #[s_fvar] body.mvarId!
      root.mvarId!.assign (Lean.mkLambda `s .default nat (mkApp rootAux (.bvar 0)))
      return root

-- Instantiate and verify sharing
run_meta do
  let root ← mkTestRoot
  let result ← instantiateMVars root

  -- Result: fun (s : Nat) => @And.intro leftTy rightTy left right
  let outerBody := result.bindingBody!
  let rightTy := outerBody.appFn!.appFn!.appArg!
  let leftTy := outerBody.appFn!.appFn!.appFn!.appArg!
  let left := outerBody.appFn!.appArg!

  -- At depth 1: rightTy, leftTy.domain, and left.domain are all
  -- instantiations of the shared `eq_ss` at the same depth → ptrEq.
  unless unsafe ptrEq rightTy leftTy.bindingDomain! do
    throwError "sharing: rightTy and leftTy.domain are not ptrEq"
  unless unsafe ptrEq rightTy left.bindingDomain! do
    throwError "sharing: rightTy and left.domain are not ptrEq"

  -- At depth 2: the two eq_ss args inside `And` in leftTy's body → ptrEq.
  let andInLeftTyBody := leftTy.bindingBody!
  unless unsafe ptrEq andInLeftTyBody.appFn!.appArg! andInLeftTyBody.appArg! do
    throwError "sharing: And args in leftTy body are not ptrEq"

  -- At depth 2: the two type args inside `And.intro` in the inner body → ptrEq.
  let innerBody := left.bindingBody!
  let innerTyArg1 := innerBody.appFn!.appFn!.appFn!.appArg!
  let innerTyArg2 := innerBody.appFn!.appFn!.appArg!
  unless unsafe ptrEq innerTyArg1 innerTyArg2 do
    throwError "sharing: And.intro type args in inner body are not ptrEq"

  -- Cross-expression: depth-2 eq_ss from leftTy body and inner body should
  -- be the same object (same shared input at the same binding depth).
  unless unsafe ptrEq andInLeftTyBody.appArg! innerTyArg1 do
    throwError "sharing: eq_ss at depth 2 not shared across leftTy and inner"
