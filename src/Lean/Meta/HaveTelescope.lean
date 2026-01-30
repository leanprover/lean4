/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller, Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Basic
public import Lean.Meta.MonadSimp
import Lean.Util.CollectFVars
import Lean.Util.CollectLooseBVars
import Lean.Meta.InferType
import Lean.Meta.AppBuilder
public section
namespace Lean.Meta
/-!
Support for representing `HaveTelescope`s and simplifying them.
We use this module to implement both `Sym.simp` and `Meta.simp` using the `MonadSimp` adapter.
-/

/--
Information about a single `have` in a `have` telescope.
Created by `getHaveTelescopeInfo`.
-/
structure HaveInfo where
  /-- Previous `have`s that the type of this `have` depends on, as indices into `HaveTelescopeInfo.haveInfo`.
  Used in `computeFixedUsed` to compute used `have`s. -/
  typeBackDeps : Std.HashSet Nat
  /-- Previous `have`s that the value of this `have` depends on, as indices into `HaveTelescopeInfo.haveInfo`.
  Used in `computeFixedUsed` to compute used `have`s. -/
  valueBackDeps : Std.HashSet Nat
  /-- The local decl for the `have`, so that the local context can be re-entered `have`-by-`have`.
  N.B. This stores the fvarid for the `have` as well as cached versions of the value and type
  instantiated with the fvars from the telescope. -/
  decl : LocalDecl
  /-- The level of the type for this `have`, cached. -/
  level : Level
  deriving Inhabited

/--
Information about a `have` telescope.
Created by `getHaveTelescopeInfo` and used in `simpHaveTelescope`.

The data is used to avoid applying `Expr.abstract` more than once on any given subexpression
when constructing terms and proofs during simplification. Abstraction is linear in the size `t` of a term,
and so in a depth-`n` telescope it is `O(nt)`, quadratic in `n`, since `n ≤ t`.
For example, given `have x₁ := v₁; ...; have xₙ := vₙ; b` and `h : b = b'`, we need to construct
```lean
have_body_congr (fun x₁ => ... have_body_congr (fun xₙ => h)))
```
We apply `Expr.abstract` to `h` *once* and then build the term, rather than
using `mkLambdaFVars #[fvarᵢ] pfᵢ` at each step.

As an additional optimization, we save the fvar-instantiated terms calculated by `getHaveTelescopeInfo`
so that we don't have to compute them again. This is only saving a constant factor.

It is also used for computing used `have`s in `computeFixedUsed`.
In `have x₁ := v; have x₂ := x₁; ⋯; have xₙ := xₙ₋₁; b`, if `xₙ` is unused in `b`, then all the
`have`s are unused. Without a global computation of used `have`s, the proof term would be quadratic
in the number of `have`s (with `n` iterations of `simp`). Knowing which `have`s are transitively
unused lets the proof term be linear in size.
-/
structure HaveTelescopeInfo where
  /-- Information about each `have` in the telescope. -/
  haveInfo : Array HaveInfo := #[]
  /-- The set of `have`s that the body depends on, as indices into `haveInfo`.
  Used in `computeFixedUsed` to compute used `have`s. -/
  bodyDeps : Std.HashSet Nat := {}
  /-- The set of `have`s that the type of the body depends on, as indices into `haveInfo`.
  This is the set of fixed `have`s. -/
  bodyTypeDeps : Std.HashSet Nat := {}
  /-- A cached version of the telescope body, instantiated with fvars from each `HaveInfo.decl`. -/
  body : Expr := Expr.const `_have_telescope_info_dummy_ []
  /-- A cached version of the telescope body's type, instantiated with fvars from each `HaveInfo.decl`. -/
  bodyType : Expr := Expr.const `_have_telescope_info_dummy_ []
  /-- The universe level for the `have` expression, cached. -/
  level : Level := Level.param `_have_telescope_info_dummy_
  deriving Inhabited

/--
Efficiently collect dependency information for a `have` telescope.
This is part of a scheme to avoid quadratic overhead from the locally nameless discipline
(see `HaveTelescopeInfo` and `simpHaveTelescope`).

The expression `e` must not have loose bvars.
-/
def getHaveTelescopeInfo (e : Expr) : MetaM HaveTelescopeInfo := do
  collect e 0 {} (← getLCtx) #[]
where
  collect (e : Expr) (numHaves : Nat) (info : HaveTelescopeInfo) (lctx : LocalContext) (fvars : Array Expr) : MetaM HaveTelescopeInfo := do
    /-
    Gives indices into `fvars` that the uninstantiated expression `a` depends on, from collecting its bvars.
    This is more efficient than collecting `fvars` from an instantiated expression,
    since the expression likely contains many fvars for the pre-existing local context.
    -/
    let getBackDeps (a : Expr) : Std.HashSet Nat :=
      a.collectLooseBVars.fold (init := {}) fun deps vidx =>
        -- Since the original expression has no bvars, `vidx < numHaves` must be true.
        deps.insert (numHaves - vidx - 1)
    match e with
    | .letE n t v b true =>
      let typeBackDeps := getBackDeps t
      let valueBackDeps := getBackDeps v
      let t := t.instantiateRev fvars
      let v := v.instantiateRev fvars
      let level ← withLCtx' lctx <| getLevel t
      let fvarId ← mkFreshFVarId
      let decl := LocalDecl.ldecl 0 fvarId n t v true .default
      let info := { info with haveInfo := info.haveInfo.push { typeBackDeps, valueBackDeps, decl, level } }
      let lctx := lctx.addDecl decl
      let fvars := fvars.push (mkFVar fvarId)
      collect b (numHaves + 1) info lctx fvars
    | _ =>
      let bodyDeps := getBackDeps e
      withLCtx' lctx do
        let body := e.instantiateRev fvars
        let bodyType ← inferType body
        let level ← getLevel bodyType
        -- Collect fvars appearing in the type of `e`. Computing `bodyType` in particular is where `MetaM` is necessary.
        let bodyTypeFVarIds := (collectFVars {} bodyType).fvarSet
        let bodyTypeDeps : Std.HashSet Nat := Nat.fold fvars.size (init := {}) fun idx _ deps =>
          if bodyTypeFVarIds.contains fvars[idx].fvarId! then
            deps.insert idx
          else
            deps
        return { info with bodyDeps, bodyTypeDeps, body, bodyType, level }

/--
Computes which `have`s in the telescope are fixed and which are unused.
The length of the unused array may be less than the number of `have`s: use `unused.getD i true`.
-/
def HaveTelescopeInfo.computeFixedUsed (info : HaveTelescopeInfo) (keepUnused : Bool) :
    MetaM (Array Bool × Array Bool) := do
  let fixed ← go info.bodyTypeDeps
  if keepUnused then
    return (fixed, #[])
  else
    let used ← go info.bodyDeps
    return (fixed, used)
where
  updateArrayFromBackDeps (arr : Array Bool) (s : Std.HashSet Nat) : Array Bool :=
    s.fold (init := arr) fun arr idx => arr.set! idx true
  go init : MetaM (Array Bool) := do
    let numHaves := info.haveInfo.size
    let mut used : Array Bool := Array.replicate numHaves false
    -- Initialize `used` with the body's dependencies.
    -- There is no need to consider `info.bodyTypeDeps` in this computation.
    used := updateArrayFromBackDeps used init
    -- For each used `have`, in reverse order, update `used`.
    for i in *...numHaves do
      let idx := numHaves - i - 1
      if used[idx]! then
        let hinfo := info.haveInfo[idx]!
        used := updateArrayFromBackDeps used hinfo.typeBackDeps
        used := updateArrayFromBackDeps used hinfo.valueBackDeps
    return used

/--
Auxiliary structure used to represent the return value of `simpHaveTelescopeAux`.
See `simpHaveTelescope` for an overview and `HaveTelescopeInfo` for an example.
-/
private structure SimpHaveResult where
  /--
  The simplified expression in `(fun x => b) v` form. Note that it may contain loose bound variables.
  `simpHaveTelescope` attempts to minimize the quadratic overhead imposed
  by the locally nameless discipline in a sequence of `have` expressions.
  -/
  expr     : Expr
  /--
  The type of `expr`. It may contain loose bound variables like in the `expr` field.
  Used in proof construction.
  -/
  exprType : Expr
  /--
  The initial expression in `(fun x => b) v` form.
  -/
  exprInit   : Expr
  /--
  The expression `expr` in `have x := v; b` form.
  -/
  exprResult : Expr
  /--
  The proof that the simplified expression is equal to the input one.
  It may contain loose bound variables like in the `expr` field.
  -/
  proof    : Expr
  /--
  `modified := false` iff `expr` is structurally equal to the input expression.
  When false, `proof` is `Eq.refl`.
  -/
  modified : Bool

  /-
  Re-enters the telescope recorded in `info` using `withExistingLocalDecls` while simplifying according to `fixed`/`used`.
  Note that we must use the low-level `Expr` APIs because the expressions may contain loose bound variables.
  Note also that we don't enter the body's local context all at once, since we need to be sure that
  when we simplify values they have their correct local context.
  -/
  deriving Inhabited

variable {m} [Monad m] [MonadLiftT MetaM m] [MonadControlT MetaM m] [MonadSimp m]

/-
Re-enters the telescope recorded in `info` using `withExistingLocalDecls` while simplifying according to `fixed`/`used`.
Note that we must use the low-level `Expr` APIs because the expressions may contain loose bound variables.
Note also that we don't enter the body's local context all at once, since we need to be sure that
when we simplify values they have their correct local context.
-/
private def simpHaveTelescopeAux (info : HaveTelescopeInfo) (fixed : Array Bool) (used : Array Bool)
      (e : Expr) (i : Nat) (xs : Array Expr) : m SimpHaveResult := do
  if h : i < info.haveInfo.size then
    let hinfo := info.haveInfo[i]
    -- `x` and `val` are the fvar and value with respect to the local context.
    let x := hinfo.decl.toExpr
    let val := hinfo.decl.value true
    -- Invariant: `v == val.abstract xs`.
    let .letE n t v b true := e | unreachable!
    -- Universe levels to use for each of the `have_*` theorems. It's the level of `val` and the level of the body.
    let us := [hinfo.level, info.level]
    if !used.getD i true then
      /-
      Unused `have`: do not add `x` to the local context then `simp` only the body.
      -/
      (do trace[Debug.Meta.Tactic.simp] "have telescope; unused {n} := {val}" : MetaM _)
      /-
      Complication: Unused `have`s might only be transitively unused.
      This means that `b.hasLooseBVar 0` might actually be true.
      This matters because `t` and `v` appear in the proof term.
      We use a dummy `x` for debugging purposes. (Recall that `Expr.abstract` skips non-fvar/mvars.)
      -/
      let x := mkConst `_simp_let_unused_dummy
      let rb ← simpHaveTelescopeAux info fixed used b (i + 1) (xs.push x)
      -- TODO(kmill): This is a source of quadratic complexity. It might be possible to avoid this,
      -- but we will need to carefully re-review the logic (note that `rb.proof` still refers to `x`).
      let expr := rb.expr.lowerLooseBVars 1 1
      let exprType := rb.exprType.lowerLooseBVars 1 1
      let exprInit := mkApp (mkLambda n .default t rb.exprInit) v
      let exprResult := rb.exprResult.lowerLooseBVars 1 1
      if rb.modified then
        let proof := mkApp6 (mkConst ``have_unused_dep' us) t exprType v (mkLambda n .default t rb.exprInit) expr
          (mkLambda n .default t rb.proof)
        return { expr, exprType, exprInit, exprResult, proof, modified := true }
      else
        -- If not modified, this must have been a non-transitively unused `have`, so no need for `dep` form.
        let proof := mkApp6 (mkConst ``have_unused' us) t exprType v expr expr
          (mkApp2 (mkConst ``Eq.refl [info.level]) exprType expr)
        return { expr, exprType, exprInit, exprResult, proof, modified := true }
    else if fixed.getD i true then
      /-
      Fixed `have` (like `CongrArgKind.fixed`): dsimp the value and simp the body.
      The variable appears in the type of the body.
      -/
      let val' ← MonadSimp.dsimp val
      (do trace[Debug.Meta.Tactic.simp] "have telescope; fixed {n} := {val} => {val'}" : MetaM _)
      let vModified := val != val'
      let v' := if vModified then val'.abstract xs else v
      withExistingLocalDecls [hinfo.decl] <| MonadSimp.withNewLemmas #[x] do
        let rb ← simpHaveTelescopeAux info fixed used b (i + 1) (xs.push x)
        let expr := mkApp (mkLambda n .default t rb.expr) v'
        let exprType := mkApp (mkLambda n .default t rb.exprType) v'
        let exprInit := mkApp (mkLambda n .default t rb.exprInit) v
        let exprResult := mkHave n t v' rb.exprResult
        -- Note: if `vModified`, then the kernel will reduce the telescopes and potentially do an expensive defeq check.
        -- If this is a performance issue, we could try using a `letFun` encoding here make use of the `is_def_eq_args` optimization.
        -- Namely, to guide the defeqs via the sequence
        --   `(fun x => b) v` = `letFun (fun x => b) v` = `letFun (fun x => b) v'` = `(fun x => b) v'`
        if rb.modified then
          let proof := mkApp6 (mkConst ``have_body_congr_dep' us) t (mkLambda n .default t rb.exprType) v'
            (mkLambda n .default t rb.exprInit) (mkLambda n .default t rb.expr) (mkLambda n .default t rb.proof)
          return { expr, exprType, exprInit, exprResult, proof, modified := true }
        else
          let proof := mkApp2 (mkConst ``Eq.refl [info.level]) exprType expr
          return { expr, exprType, exprInit, exprResult, proof, modified := vModified }
    else
      /-
      Non-fixed `have` (like `CongrArgKind.eq`): simp both the value and the body.
      The variable does not appear in the type of the body.
      -/
      let (v', valModified, vproof) ← match (← MonadSimp.simp val) with
        | .rfl => pure (v, false, mkApp2 (mkConst `Eq.refl [hinfo.level]) t v)
        | .step val' h =>
          (do trace[Debug.Meta.Tactic.simp] "have telescope; non-fixed {n} := {val} => {val'}" : MetaM _)
          pure (val'.abstract xs, true, h.abstract xs)
      withExistingLocalDecls [hinfo.decl] <| MonadSimp.withNewLemmas #[x] do
        let rb ← simpHaveTelescopeAux info fixed used b (i + 1) (xs.push x)
        let expr := mkApp (mkLambda n .default t rb.expr) v'
        assert! !rb.exprType.hasLooseBVar 0
        let exprType := rb.exprType.lowerLooseBVars 1 1
        let exprInit := mkApp (mkLambda n .default t rb.exprInit) v
        let exprResult := mkHave n t v' rb.exprResult
        match valModified, rb.modified with
        | false, false =>
          let proof := mkApp2 (mkConst `Eq.refl [info.level]) exprType expr
          return { expr, exprType, exprInit, exprResult, proof, modified := false }
        | true, false =>
          let proof := mkApp6 (mkConst ``have_val_congr' us) t exprType v v'
            (mkLambda n .default t rb.exprInit) vproof
          return { expr, exprType, exprInit, exprResult, proof, modified := true }
        | false, true =>
          let proof := mkApp6 (mkConst ``have_body_congr' us) t exprType v
            (mkLambda n .default t rb.exprInit) (mkLambda n .default t rb.expr) (mkLambda n .default t rb.proof)
          return { expr, exprType, exprInit, exprResult, proof, modified := true }
        | true, true =>
          let proof := mkApp8 (mkConst ``have_congr' us) t exprType v v'
            (mkLambda n .default t rb.exprInit) (mkLambda n .default t rb.expr) vproof (mkLambda n .default t rb.proof)
          return { expr, exprType, exprInit, exprResult, proof, modified := true }
  else
    -- Base case: simplify the body.
    (do trace[Debug.Meta.Tactic.simp] "have telescope; simplifying body {info.body}" : MetaM _)
    let exprType := info.bodyType.abstract xs
    match (← MonadSimp.simp info.body) with
    | .rfl =>
      let proof := mkApp2 (mkConst `Eq.refl [info.level]) exprType e
      return { expr := e, exprType, exprInit := e, exprResult := e, proof, modified := false }
    | .step body' h =>
      let expr := body'.abstract xs
      let proof := h.abstract xs
      -- Optimization: if the proof is a `simpHaveTelescope` proof, then remove the type hint
      -- to avoid the zeta/beta reductions that the kernel would otherwise do.
      -- In `SimpHaveResult.toResult` we insert two type hints; the inner one
      -- encodes the `exprInit` and `expr`.
      let detectSimpHaveLemma (proof : Expr) : Option SimpHaveResult := do
        let_expr id eq proof' := proof | failure
        guard <| eq.isAppOfArity ``Eq 3
        let_expr id eq' proof'' := proof' | failure
        let_expr Eq _ lhs rhs := eq' | failure
        let .const n _ := proof''.getAppFn | failure
        guard (n matches ``have_unused_dep' | ``have_unused' | ``have_body_congr_dep' | ``have_val_congr' | ``have_body_congr' | ``have_congr')
        return { expr := rhs, exprType, exprInit := lhs, exprResult := expr, proof := proof'', modified := true }
      if let some res := detectSimpHaveLemma proof then
        return res
      return { expr, exprType, exprInit := e, exprResult := expr, proof, modified := true }

/-- Configuration for specifying how unused let-declarations are eliminated. -/
inductive ZetaUnusedMode where
  | /-- Do not eliminate unused `let`-declarations. -/
    no
  | /-- Simplify and eliminate unused `let`-declarations in a single pass. -/
    singlePass
  | /-- Simplify and then eliminate unused `let`-declarations. -/
    twoPasses

/-- Remove unused-let declarations. -/
def zetaUnused (e : Expr) : MetaM Expr := do
  letTelescope e fun xs body => do
    let mut s := collectFVars {} body
    let mut ys := #[]
    let mut i := xs.size
    while i > 0 do
      i := i - 1
      let x := xs[i]!
      let xFVarId := x.fvarId!
      if s.fvarSet.contains xFVarId then
        let decl ← xFVarId.getDecl
        s  := collectFVars s decl.type
        s  := collectFVars s (decl.value (allowNondep := true))
        ys := ys.push x
    if ys.size == xs.size then
      return e
    else
      mkLetFVars (generalizeNondepLet := false) ys.reverse body

/--
Constructs the final result. If `keepUnused` is `false`, it eliminates unused let-declarations from
`exprResult` using `zetaUnused` above. This flag is used when we set `ZetaUnusedMode.twoPasses`.
-/
private def SimpHaveResult.toResult (u : Level) (source : Expr) (result : SimpHaveResult) (keepUnused : Bool) : MetaM MonadSimp.Result := do
  match result with
  | { expr, exprType, exprInit, exprResult, proof, modified, .. } =>
    if modified then
      let proof :=
          -- Add a type hint to convert back into `have` form.
          mkExpectedPropHint (expectedProp := mkApp3 (mkConst ``Eq [u]) exprType source exprResult) <|
            -- Add in a second type hint, for use in an optimization to avoid zeta/beta reductions in the kernel
            -- The base case in `simpHaveTelescopeAux` detects this construction and uses `exprType`/`exprInit`
            -- to construct the `SimpHaveResult`.
            -- If the kernel were to support `have` forms of the congruence lemmas this would not be necessary.
            mkExpectedPropHint (expectedProp := mkApp3 (mkConst ``Eq [u]) exprType exprInit expr) proof
      if keepUnused then
        return .step exprResult proof
      else
        let exprResult' ← zetaUnused exprResult
        if exprResult' == exprResult then
          return .step exprResult proof
        else
          let proof := mkApp6 (mkConst ``Eq.trans [u]) exprType source exprResult exprResult' proof
            (mkApp2 (mkConst ``Eq.refl [u]) exprType exprResult')
          return .step exprResult' proof
    else if keepUnused then
      return .rfl
    else
      let exprResult ← zetaUnused source
      if exprResult == source then
        return .rfl
      else
        let proof := mkApp2 (mkConst ``Eq.refl [u]) exprType exprResult
        return .step exprResult proof

/--
Routine for simplifying `have` telescopes. Used by `simpLet`.
This is optimized to be able to handle deep `have` telescopes while avoiding quadratic complexity
arising from the locally nameless expression representations.

## Overview

Consider a `have` telescope:
```
have x₁ : T₁ := v₁; ...; have xₙ : Tₙ := vₙ; b
```
We say `xᵢ` is *fixed* if it appears in the type of `b`.
If `xᵢ` is fixed, then it can only be rewritten using definitional equalities.
Otherwise, we can freely rewrite the value using a propositional equality `vᵢ = vᵢ'`.
The body `b` can always be freely rewritten using a propositional equality `b = b'`.
(All the mentioned equalities must be type correct with respect to the obvious local contexts.)

If `xᵢ` neither appears in `b` nor any `Tⱼ` nor any `vⱼ`, then its `have` is *unused*.
Unused `have`s can be eliminated, which we do if `cfg.zetaUnused` is true.
We clear `have`s from the end, to be able to transitively clear chains of unused `have`s.
This is why we honor `zetaUnused` here even though `reduceStep` is also responsible for it;
`reduceStep` can only eliminate unused `have`s at the start of a telescope.
Eliminating all transitively unused `have`s at once like this also avoids quadratic complexity.

If `debug.simp.check.have` is enabled then we typecheck the resulting expression and proof.

## Proof generation

There are two main complications with generating proofs.
1. We work almost exclusively with expressions with loose bound variables,
   to avoid overhead from instantiating and abstracting free variables,
   which can lead to complexity quadratic in the telescope length.
   (See `HaveTelescopeInfo`.)
2. We want to avoid triggering zeta reductions in the kernel.

Regarding this second point, the issue is that we cannot organize the proof using congruence theorems
in the obvious way. For example, given
```
theorem have_congr {α : Sort u} {β : Sort v} {a a' : α} {f f' : α → β}
    (h₁ : a = a') (h₂ : ∀ x, f x = f' x) :
    (have x := a; f x) = (have x := a'; f' x)
```
the kernel sees that the type of `have_congr (fun x => b) (fun x => b') h₁ h₂`
is `(have x := a; (fun x => b) x) = (have x := a'; (fun x => b') x)`,
since when instantiating values it does not beta reduce at the same time.
Hence, when `is_def_eq` is applied to the LHS and `have x := a; b` for example,
it will do `whnf_core` to both sides.

Instead, we use the form `(fun x => b) a = (fun x => b') a'` in the proofs,
which we can reliably match up without triggering beta reductions in the kernel.
The zeta/beta reductions are then limited to the type hint for the entire telescope,
when we convert this back into `have` form.
In the base case, we include an optimization to avoid unnecessary zeta/beta reductions,
by detecting a `simpHaveTelescope` proofs and removing the type hint.
-/
def simpHaveTelescope (e : Expr) (zetaUnusedMode : ZetaUnusedMode := .twoPasses) : m MonadSimp.Result := do
  let info ← getHaveTelescopeInfo e
  assert! !info.haveInfo.isEmpty
  let (fixed, used) ← info.computeFixedUsed (keepUnused := zetaUnusedMode matches .no | .twoPasses)
  let r ← simpHaveTelescopeAux info fixed used e 0 (Array.mkEmpty info.haveInfo.size)
  r.toResult info.level e (keepUnused := zetaUnusedMode matches .no | .singlePass)

end Lean.Meta
