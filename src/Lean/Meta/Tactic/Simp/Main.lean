/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
public import Lean.Meta.Tactic.Replace
public import Lean.Meta.Tactic.Simp.Rewrite
public import Lean.Meta.Tactic.Simp.Diagnostics
public import Lean.Meta.Match.Value
public import Lean.Util.CollectLooseBVars
import Lean.PrettyPrinter

public section

namespace Lean.Meta
namespace Simp

register_builtin_option backward.dsimp.proofs : Bool := {
    defValue := false
    descr    := "Let `dsimp` simplify proof terms"
  }

register_builtin_option debug.simp.check.have : Bool := {
    defValue := false
    descr    := "(simp) enable consistency checks for `have` telescope simplification"
  }

builtin_initialize congrHypothesisExceptionId : InternalExceptionId ←
  registerInternalExceptionId `congrHypothesisFailed

def throwCongrHypothesisFailed : MetaM α :=
  throw <| Exception.internal congrHypothesisExceptionId

/-- Return true if `e` is of the form `ofNat n` where `n` is a kernel Nat literal -/
def isOfNatNatLit (e : Expr) : Bool :=
  e.isAppOf ``OfNat.ofNat && e.getAppNumArgs >= 3 && (e.getArg! 1).isRawNatLit

/--
If `e` is a raw Nat literal and `OfNat.ofNat` is not in the list of declarations to unfold,
return an `OfNat.ofNat`-application.
-/
def foldRawNatLit (e : Expr) : SimpM Expr := do
  match e.rawNatLit? with
  | some n =>
    /- If `OfNat.ofNat` is marked to be unfolded, we do not pack orphan nat literals as `OfNat.ofNat` applications
        to avoid non-termination. See issue #788.  -/
    if (← readThe Simp.Context).isDeclToUnfold ``OfNat.ofNat then
      return e
    else
      return toExpr n
  | none   => return e

/-- Return true if `e` is of the form `ofScientific n b m` where `n` and `m` are kernel Nat literals. -/
def isOfScientificLit (e : Expr) : Bool :=
  e.isAppOfArity ``OfScientific.ofScientific 5 && (e.getArg! 4).isRawNatLit && (e.getArg! 2).isRawNatLit

/-- Return true if `e` is of the form `Char.ofNat n` where `n` is a kernel Nat literals. -/
def isCharLit (e : Expr) : Bool :=
  e.isAppOfArity ``Char.ofNat 1 && e.appArg!.isRawNatLit

/--
Unfold definition even if it is not marked as `@[reducible]`.
Remark: We never unfold irreducible definitions. Mathlib relies on that in the implementation of the
command `irreducible_def`.
-/
private def unfoldDefinitionAny? (e : Expr) : MetaM (Option Expr) := do
  if let .const declName _ := e.getAppFn then
    if (← isIrreducible declName) then
      return none
  unfoldDefinition? e (ignoreTransparency := true)

private def reduceProjFn? (e : Expr) : SimpM (Option Expr) := do
  matchConst e.getAppFn (fun _ => pure none) fun cinfo _ => do
    match (← getProjectionFnInfo? cinfo.name) with
    | none => return none
    | some projInfo =>
      /- Helper function for applying `reduceProj?` to the result of `unfoldDefinition?` -/
      let reduceProjCont? (e? : Option Expr) : SimpM (Option Expr) := do
        match e? with
        | none   => pure none
        | some e =>
          match (← withSimpMetaConfig <| reduceProj? e.getAppFn) with
          | some f => return some (mkAppN f e.getAppArgs)
          | none   => return none
      if projInfo.fromClass then
        -- `class` projection
        if (← getContext).isDeclToUnfold cinfo.name then
          /-
          If user requested `class` projection to be unfolded, we set transparency mode to `.instances`,
          and invoke `unfoldDefinition?`.
          Recall that `unfoldDefinition?` has support for unfolding this kind of projection when transparency mode is `.instances`.
          -/
          let e? ← withReducibleAndInstances <| unfoldDefinition? e
          if e?.isSome then
            recordSimpTheorem (.decl cinfo.name)
          return e?
        else
          /-
          Recall that class projections are **not** marked with `[reducible]` because we want them to be
          in "reducible canonical form". However, if we have a class projection of the form `Class.projFn (Class.mk ...)`,
          we want to reduce it. See issue #1869 for an example where this is important.
          -/
          unless e.getAppNumArgs > projInfo.numParams do
            return none
          let major := e.getArg! projInfo.numParams
          unless (← isConstructorApp major) do
            return none
          reduceProjCont? (← unfoldDefinitionAny? e)
      else
        -- `structure` projections
        reduceProjCont? (← unfoldDefinition? e)

private def reduceFVar (cfg : Config) (thms : SimpTheoremsArray) (e : Expr) : SimpM Expr := do
  let localDecl ← getFVarLocalDecl e
  if cfg.zetaDelta || thms.isLetDeclToUnfold e.fvarId! || localDecl.isImplementationDetail then
    if !cfg.zetaDelta && thms.isLetDeclToUnfold e.fvarId! then
      recordSimpTheorem (.fvar localDecl.fvarId)
    let some v := localDecl.value? | return e
    return v
  else
    return e

/--
  Return true if `declName` is the name of a definition of the form
  ```
  def declName ... :=
    match ... with
    | ...
  ```
-/
private partial def isMatchDef (declName : Name) : CoreM Bool := do
  let .defnInfo info ← getConstInfo declName | return false
  return go (← getEnv) info.value
where
  go (env : Environment) (e : Expr) : Bool :=
    if e.isLambda then
      go env e.bindingBody!
    else
      let f := e.getAppFn
      f.isConst && isMatcherCore env f.constName!

/--
Try to unfold `e`.
-/
private def unfold? (e : Expr) : SimpM (Option Expr) := do
  let f := e.getAppFn
  if !f.isConst then
    return none
  let fName := f.constName!
  let ctx ← getContext
  let rec unfoldDeclToUnfold? : SimpM (Option Expr) := do
    let options ← getOptions
    let cfg ← getConfig
    -- Support for issue #2042
    if cfg.unfoldPartialApp -- If we are unfolding partial applications, ignore issue #2042
       -- When smart unfolding is enabled, and `f` supports it, we don't need to worry about issue #2042
       || (smartUnfolding.get options && (← getEnv).contains (mkSmartUnfoldingNameFor fName)) then
      unfoldDefinitionAny? e
    else
      -- We are not unfolding partial applications, and `fName` does not have smart unfolding support.
      -- Thus, we must check whether the arity of the function >= number of arguments.
      let some cinfo := (← getEnv).find? fName | return none
      let some value := cinfo.value? | return none
      let arity := value.getNumHeadLambdas
      -- Partially applied function, return `none`. See issue #2042
      if arity > e.getAppNumArgs then return none
      unfoldDefinitionAny? e
  if (← isProjectionFn fName) then
    return none -- should be reduced by `reduceProjFn?`
  else if ctx.config.autoUnfold then
    if ctx.simpTheorems.isErased (.decl fName) then
      return none
    else if hasSmartUnfoldingDecl (← getEnv) fName then
      unfoldDefinitionAny? e
    else if (← isMatchDef fName) then
      let some value ← unfoldDefinitionAny? e | return none
      let .reduced value ← withSimpMetaConfig <| reduceMatcher? value | return none
      return some value
    else
      return none
  else if ctx.isDeclToUnfold fName then
    unfoldDeclToUnfold?
  else
    return none

private def reduceStep (e : Expr) : SimpM Expr := do
  let cfg ← getConfig
  let f := e.getAppFn
  if f.isMVar then
    return (← instantiateMVars e)
  withSimpMetaConfig do
  if cfg.beta then
    if f.isHeadBetaTargetFn false then
      return f.betaRev e.getAppRevArgs
  -- TODO: eta reduction
  if cfg.proj then
    match (← reduceProj? e) with
    | some e => return e
    | none =>
    match (← reduceProjFn? e) with
    | some e => return e
    | none   => pure ()
  if cfg.iota then
    match (← reduceRecMatcher? e) with
    | some e => return e
    | none   => pure ()
  if let .letE _ _ v b nondep := e then
    if cfg.zeta && (!nondep || cfg.zetaHave) then
      return expandLet b #[v] (zetaHave := cfg.zetaHave)
    else if cfg.zetaUnused && !b.hasLooseBVars then
      return consumeUnusedLet b
  match (← unfold? e) with
  | some e' =>
    trace[Meta.Tactic.simp.rewrite] "unfold {.ofConst e.getAppFn}, {e} ==> {e'}"
    recordSimpTheorem (.decl e.getAppFn.constName!)
    return e'
  | none => foldRawNatLit e

private partial def reduce (e : Expr) : SimpM Expr := withIncRecDepth do
  let e' ← reduceStep e
  if e' == e then
    return e'
  else
    trace[Debug.Meta.Tactic.simp] "reduce {e} => {e'}"
    reduce e'

instance : Inhabited (SimpM α) where
  default := fun _ _ _ => default

partial def lambdaTelescopeDSimp (e : Expr) (k : Array Expr → Expr → SimpM α) : SimpM α := do
  go #[] e
where
  go (xs : Array Expr) (e : Expr) : SimpM α := do
    match e with
    | .lam n d b c => withLocalDecl n c (← dsimp d) fun x => go (xs.push x) (b.instantiate1 x)
    | e => k xs e

/--
We use `withNewLemmas` whenever updating the local context.
-/
def withNewLemmas {α} (xs : Array Expr) (f : SimpM α) : SimpM α := do
  if (← getConfig).contextual then
    withFreshCache do
      let mut s ← getSimpTheorems
      let mut updated := false
      let ctx ← getContext
      for x in xs do
        if (← isProof x) then
          s ← s.addTheorem (.fvar x.fvarId!) x (config := ctx.indexConfig)
          updated := true
      if updated then
        withSimpTheorems s f
      else
        f
  else if (← getMethods).wellBehavedDischarge then
    -- See comment at `Methods.wellBehavedDischarge` to understand why
    -- we don't have to reset the cache
    f
  else
    withFreshCache do f

def simpProj (e : Expr) : SimpM Result := do
  match (← withSimpMetaConfig <| reduceProj? e) with
  | some e => return { expr := e }
  | none =>
    let s := e.projExpr!
    let motive? ← withLocalDeclD `s (← inferType s) fun s => do
      let p := e.updateProj! s
      if (← dependsOn (← inferType p) s.fvarId!) then
        return none
      else
        let motive ← mkLambdaFVars #[s] (← mkEq e p)
        if !(← isTypeCorrect motive) then
          return none
        else
          return some motive
    if let some motive := motive? then
      let r ← simp s
      let eNew := e.updateProj! r.expr
      match r.proof? with
      | none => return { expr := eNew }
      | some h =>
        let hNew ← mkEqNDRec motive (← mkEqRefl e) h
        return { expr := eNew, proof? := some hNew }
    else
      return { expr := (← dsimp e) }

def simpConst (e : Expr) : SimpM Result :=
  return { expr := (← reduce e) }

def simpLambda (e : Expr) : SimpM Result :=
  withParent e <| lambdaTelescopeDSimp e fun xs e => withNewLemmas xs do
    let r ← simp e
    r.addLambdas xs

def simpArrow (e : Expr) : SimpM Result := do
  trace[Debug.Meta.Tactic.simp] "arrow {e}"
  let p := e.bindingDomain!
  let q := e.bindingBody!
  let rp ← simp p
  trace[Debug.Meta.Tactic.simp] "arrow [{(← getConfig).contextual}] {p} [{← isProp p}] -> {q} [{← isProp q}]"
  if (← pure (← getConfig).contextual <&&> isProp p <&&> isProp q) then
    trace[Debug.Meta.Tactic.simp] "ctx arrow {rp.expr} -> {q}"
    withLocalDeclD e.bindingName! rp.expr fun h => withNewLemmas #[h] do
      let rq ← simp q
      match rq.proof? with
      | none    => mkImpCongr e rp rq
      | some hq =>
        let hq ← mkLambdaFVars #[h] hq
        /-
          We use the default reducibility setting at `mkImpDepCongrCtx` and `mkImpCongrCtx` because they use the theorems
          ```lean
          @implies_dep_congr_ctx : ∀ {p₁ p₂ q₁ : Prop}, p₁ = p₂ → ∀ {q₂ : p₂ → Prop}, (∀ (h : p₂), q₁ = q₂ h) → (p₁ → q₁) = ∀ (h : p₂), q₂ h
          @implies_congr_ctx : ∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p₁ → q₁) = (p₂ → q₂)
          ```
          And the proofs may be from `rfl` theorems which are now omitted. Moreover, we cannot establish that the two
          terms are definitionally equal using `withReducible`.
          TODO (better solution): provide the problematic implicit arguments explicitly. It is more efficient and avoids this
          problem.
          -/
        if rq.expr.containsFVar h.fvarId! then
          return { expr := (← mkForallFVars #[h] rq.expr), proof? := (← withDefault <| mkImpDepCongrCtx (← rp.getProof) hq) }
        else
          return { expr := e.updateForallE! rp.expr rq.expr, proof? := (← withDefault <| mkImpCongrCtx (← rp.getProof) hq) }
  else
    mkImpCongr e rp (← simp q)

def simpForall (e : Expr) : SimpM Result := withParent e do
  trace[Debug.Meta.Tactic.simp] "forall {e}"
  if e.isArrow then
    simpArrow e
  else
    let domain := e.bindingDomain!
    if (← isProp e) && (← isProp domain) then
      /-
      The domain and codomain of the forall are propositions, and we can use `forall_prop_domain_congr`
      IF we can simplify the domain.
      -/
      let rd ← simp domain
      if let some h₁ := rd.proof? then
        /- Using
        ```
        theorem forall_prop_domain_congr {p₁ p₂ : Prop} {q₁ : p₁ → Prop} {q₂ : p₂ → Prop}
            (h₁ : p₁ = p₂)
            (h₂ : ∀ a : p₂, q₁ (h₁.substr a) = q₂ a)
            : (∀ a : p₁, q₁ a) = (∀ a : p₂, q₂ a)
        ```
        Remark: we should consider whether we want to add congruence lemma support for arbitrary `forall`-expressions.
        Then, the theroem above can be marked as `@[congr]` and the following code deleted.
        -/
        let p₁ := domain
        let p₂ := rd.expr
        let q₁ := mkLambda e.bindingName! e.bindingInfo! p₁ e.bindingBody!
        let result ← withLocalDecl e.bindingName! e.bindingInfo! p₂ fun a => withNewLemmas #[a] do
          let prop := mkSort levelZero
          let h₁_substr_a := mkApp6 (mkConst ``Eq.substr [levelOne]) prop (mkLambda `x .default prop (mkBVar 0)) p₂ p₁ h₁ a
          let q_h₁_substr_a := e.bindingBody!.instantiate1 h₁_substr_a
          let rb ← simp q_h₁_substr_a
          let h₂ ← mkLambdaFVars #[a] (← rb.getProof)
          let q₂ ← mkLambdaFVars #[a] rb.expr
          let result ← mkForallFVars #[a] rb.expr
          let proof := mkApp6 (mkConst ``forall_prop_domain_congr) p₁ p₂ q₁ q₂ h₁ h₂
          return { expr := result, proof? := proof }
        return result
    let domain ← dsimp domain
    withLocalDecl e.bindingName! e.bindingInfo! domain fun x => withNewLemmas #[x] do
      let b := e.bindingBody!.instantiate1 x
      let rb ← simp b
      let eNew ← mkForallFVars #[x] rb.expr
      match rb.proof? with
      | none   => return { expr := eNew }
      | some h => return { expr := eNew, proof? := (← mkPiCongr (← mkLambdaFVars #[x] h)) }

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

private def SimpHaveResult.toResult (u : Level) (source : Expr) : SimpHaveResult → Result
  | { expr, exprType, exprInit, exprResult, proof, modified, .. } =>
    { expr := exprResult
      proof? :=
        if modified then
          -- Add a type hint to convert back into `have` form.
          some <| mkExpectedPropHint (expectedProp := mkApp3 (mkConst ``Eq [u]) exprType source exprResult) <|
            -- Add in a second type hint, for use in an optimization to avoid zeta/beta reductions in the kernel
            -- The base case in `simpHaveTelescopeAux` detects this construction and uses `exprType`/`exprInit`
            -- to construct the `SimpHaveResult`.
            -- If the kernel were to support `have` forms of the congruence lemmas this would not be necessary.
            mkExpectedPropHint (expectedProp := mkApp3 (mkConst ``Eq [u]) exprType exprInit expr) proof
        else
          none }

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
def simpHaveTelescope (e : Expr) : SimpM Result := do
  Prod.fst <$> withTraceNode `Debug.Meta.Tactic.simp (fun
      | .ok (_, used, fixed, modified) => pure m!"{checkEmoji} have telescope; used: {used}; fixed: {fixed}; modified: {modified}"
      | .error ex => pure m!"{crossEmoji} {ex.toMessageData}") do
    let info ← getHaveTelescopeInfo e
    assert! !info.haveInfo.isEmpty
    let (fixed, used) ← info.computeFixedUsed (keepUnused := !(← getConfig).zetaUnused)
    let r ← simpHaveTelescopeAux info fixed used e 0 (Array.mkEmpty info.haveInfo.size)
    if r.modified && debug.simp.check.have.get (← getOptions) then
      check r.expr
      check r.proof
    return (r.toResult info.level e, used, fixed, r.modified)
where
  /-
  Re-enters the telescope recorded in `info` using `withExistingLocalDecls` while simplifying according to `fixed`/`used`.
  Note that we must use the low-level `Expr` APIs because the expressions may contain loose bound variables.
  Note also that we don't enter the body's local context all at once, since we need to be sure that
  when we simplify values they have their correct local context.
  -/
  simpHaveTelescopeAux (info : HaveTelescopeInfo) (fixed : Array Bool) (used : Array Bool) (e : Expr) (i : Nat) (xs : Array Expr) : SimpM SimpHaveResult := do
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
        trace[Debug.Meta.Tactic.simp] "have telescope; unused {n} := {val}"
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
        let val' ← dsimp val
        trace[Debug.Meta.Tactic.simp] "have telescope; fixed {n} := {val} => {val'}"
        let vModified := val != val'
        let v' := if vModified then val'.abstract xs else v
        withExistingLocalDecls [hinfo.decl] <| withNewLemmas #[x] do
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
        let rval' ← simp val
        trace[Debug.Meta.Tactic.simp] "have telescope; non-fixed {n} := {val} => {rval'.expr}"
        let valModified := rval'.expr != val
        let v' := if valModified then rval'.expr.abstract xs else v
        let vproof ← if valModified then
          pure <| (← rval'.getProof).abstract xs
        else
          pure <| mkApp2 (mkConst `Eq.refl [hinfo.level]) t v
        withExistingLocalDecls [hinfo.decl] <| withNewLemmas #[x] do
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
      trace[Debug.Meta.Tactic.simp] "have telescope; simplifying body {info.body}"
      let r ← simp info.body
      let exprType := info.bodyType.abstract xs
      if r.expr == info.body then
        let proof := mkApp2 (mkConst `Eq.refl [info.level]) exprType e
        return { expr := e, exprType, exprInit := e, exprResult := e, proof, modified := false }
      else
        let expr := r.expr.abstract xs
        let proof := (← r.getProof).abstract xs
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

/--
Routine for simplifying `let` expressions.

If it is a `have`, we use `simpHaveTelescope` to simplify entire telescopes at once, to avoid quadratic behavior
arising from locally nameless expression representations.

We assume that dependent `let`s are dependent,
but if `Config.letToHave` is enabled then we attempt to transform it into a `have`.
If that does not change it, then it is only `dsimp`ed.
-/
def simpLet (e : Expr) : SimpM Result := do
  withTraceNode `Debug.Meta.Tactic.simp (return m!"{exceptEmoji ·} let{indentExpr e}") do
    assert! e.isLet
    /-
    Recall: `simpLet` is called after `reduceStep` is applied, so `simpLet` is not responsible for zeta reduction.
    Hence, the expression is a `let` or `have` that is not reducible in the current configuration.
    -/
    if e.letNondep! then
      simpHaveTelescope e
    else
      /-
      When `cfg.letToHave` is true, we use `letToHave` to decide whether or not this `let` is dependent.
      If it becomes a `have`, then we can jump right into simplifying the `have` telescope.
      -/
      let e ←
        if (← getConfig).letToHave then
          let eNew ← letToHave e
          if eNew.isLet && eNew.letNondep! then
            trace[Debug.Meta.Tactic.simp] "letToHave ==>{indentExpr eNew}"
            return ← simpHaveTelescope eNew
          pure eNew
        else
          pure e
      /-
      The `let` is dependent.
      We fall back to doing only definitional simplification.

      Note that for `let x := v; b`, if we had a rewrite `h : b = b'` given `x := v` in the local context,
      we could abstract `x` to get `(let x := v; h) : (let x := v; b = b')` and then use the fact that
      this type is definitionally equal to `(let x := v; b) = (let x := v; b')`.
      -/
      return { expr := (← dsimp e) }

private def dsimpReduce : DSimproc := fun e => do
  let mut eNew ← reduce e
  if eNew.isFVar then
    eNew ← reduceFVar (← getConfig) (← getSimpTheorems) eNew
  if eNew != e then return .visit eNew else return .done e

/-- Auxiliary `dsimproc` for not visiting proof terms. -/
private def doNotVisitProofs : DSimproc := fun e => do
  if ← isProof e then
    if !backward.dsimp.proofs.get (← getOptions) then
      return .done e
    else
      return .continue e
  else
    return .continue e

/-- Helper `dsimproc` for `doNotVisitOfNat` and `doNotVisitOfScientific` -/
private def doNotVisit (pred : Expr → Bool) (declName : Name) : DSimproc := fun e => do
  if pred e then
    if (← readThe Simp.Context).isDeclToUnfold declName then
      return .continue e
    else
      -- Users may have added a `[simp]` rfl theorem for the literal
      match (← (← getMethods).dpost e) with
      | .continue none => return .done e
      | r => return r
  else
    return .continue e

/--
Auxiliary `dsimproc` for not visiting `OfNat.ofNat` application subterms.
This is the `dsimp` equivalent of the approach used at `visitApp`.
Recall that we fold orphan raw Nat literals.
-/
private def doNotVisitOfNat : DSimproc := doNotVisit isOfNatNatLit ``OfNat.ofNat

/--
Auxiliary `dsimproc` for not visiting `OfScientific.ofScientific` application subterms.
-/
private def doNotVisitOfScientific : DSimproc := doNotVisit isOfScientificLit ``OfScientific.ofScientific

/--
Auxiliary `dsimproc` for not visiting `Char` literal subterms.
-/
private def doNotVisitCharLit : DSimproc := doNotVisit isCharLit ``Char.ofNat

@[export lean_dsimp]
private partial def dsimpImpl (e : Expr) : SimpM Expr := do
  let cfg ← getConfig
  unless cfg.dsimp do
    return e
  let m ← getMethods
  let pre := m.dpre >> doNotVisitOfNat >> doNotVisitOfScientific >> doNotVisitCharLit >> doNotVisitProofs
  let post := m.dpost >> dsimpReduce
  withInDSimpWithCache fun cache => do
    transformWithCache e cache (usedLetOnly := cfg.zeta || cfg.zetaUnused) (pre := pre) (post := post)

def visitFn (e : Expr) : SimpM Result := do
  let f := e.getAppFn
  let fNew ← simp f
  if fNew.expr == f then
    return { expr := e }
  else
    let args := e.getAppArgs
    let eNew := mkAppN fNew.expr args
    if fNew.proof?.isNone then return { expr := eNew }
    let mut proof ← fNew.getProof
    for arg in args do
      proof ← Meta.mkCongrFun proof arg
    return { expr := eNew, proof? := proof }

def congrDefault (e : Expr) : SimpM Result := do
  if let some result ← tryAutoCongrTheorem? e then
    result.mkEqTrans (← visitFn result.expr)
  else
    withParent e <| e.withApp fun f args => do
      congrArgs (← simp f) args

/-- Process the given congruence theorem hypothesis. Return true if it made "progress". -/
def processCongrHypothesis (h : Expr) (hType : Expr) : SimpM Bool := do
  forallTelescopeReducing hType fun xs hType => withNewLemmas xs do
    let lhs ← instantiateMVars hType.appFn!.appArg!
    let r ← simp lhs
    let rhs := hType.appArg!
    rhs.withApp fun m zs => do
      let val ← mkLambdaFVars zs r.expr
      unless (← withSimpMetaConfig <| isDefEq m val) do
        throwCongrHypothesisFailed
      let mut proof ← r.getProof
      if hType.isAppOf ``Iff then
        try proof ← mkIffOfEq proof
        catch _ => throwCongrHypothesisFailed
      unless (← isDefEq h (← mkLambdaFVars xs proof)) do
        throwCongrHypothesisFailed
      /- We used to return `false` if `r.proof? = none` (i.e., an implicit `rfl` proof) because we
          assumed `dsimp` would also be able to simplify the term, but this is not true
          for non-trivial user-provided theorems.
          Example:
          ```
          @[congr] theorem image_congr {f g : α → β} {s : Set α} (h : ∀ a, mem a s → f a = g a) : image f s = image g s :=
          ...

          example {Γ: Set Nat}: (image (Nat.succ ∘ Nat.succ) Γ) = (image (fun a => a.succ.succ) Γ) := by
            simp only [Function.comp_apply]
          ```
          `Function.comp_apply` is a `rfl` theorem, but `dsimp` will not apply it because the composition
          is not fully applied. See comment at issue #1113

          Thus, we have an extra check now if `xs.size > 0`. TODO: refine this test.
      -/
      return r.proof?.isSome || (xs.size > 0 && lhs != r.expr)

/-- Try to rewrite `e` children using the given congruence theorem -/
def trySimpCongrTheorem? (c : SimpCongrTheorem) (e : Expr) : SimpM (Option Result) := withNewMCtxDepth do withParent e do
  recordCongrTheorem c.theoremName
  trace[Debug.Meta.Tactic.simp.congr] "{c.theoremName}, {e}"
  let thm ← mkConstWithFreshMVarLevels c.theoremName
  let thmType ← inferType thm
  let thmHasBinderNameHint := thmType.hasBinderNameHint
  let (xs, bis, type) ← forallMetaTelescopeReducing thmType
  if c.hypothesesPos.any (· ≥ xs.size) then
    return none
  let isIff := type.isAppOf ``Iff
  let lhs := type.appFn!.appArg!
  let rhs := type.appArg!
  let numArgs := lhs.getAppNumArgs
  let mut e := e
  let mut extraArgs := #[]
  if e.getAppNumArgs > numArgs then
    let args := e.getAppArgs
    e := mkAppN e.getAppFn args[*...numArgs]
    extraArgs := args[numArgs...*].toArray
  if (← withSimpMetaConfig <| isDefEq lhs e) then
    let mut modified := false
    for i in c.hypothesesPos do
      let h := xs[i]!
      let hType ← instantiateMVars (← inferType h)
      let hType ← if thmHasBinderNameHint then hType.resolveBinderNameHint else pure hType
      try
        if (← processCongrHypothesis h hType) then
          modified := true
      catch _ =>
        trace[Meta.Tactic.simp.congr] "processCongrHypothesis {c.theoremName} failed {hType}"
        -- Remark: we don't need to check ex.isMaxRecDepth anymore since `try .. catch ..`
        -- does not catch runtime exceptions by default.
        return none
    unless modified do
      trace[Meta.Tactic.simp.congr] "{c.theoremName} not modified"
      return none
    unless (← synthesizeArgs (.decl c.theoremName) bis xs) do
      trace[Meta.Tactic.simp.congr] "{c.theoremName} synthesizeArgs failed"
      return none
    let eNew ← instantiateMVars rhs
    let mut proof ← instantiateMVars (mkAppN thm xs)
    if isIff then
      try proof ← mkAppM ``propext #[proof]
      catch _ => return none
    if (← hasAssignableMVar proof <||> hasAssignableMVar eNew) then
      trace[Meta.Tactic.simp.congr] "{c.theoremName} has unassigned metavariables"
      return none
    congrArgs { expr := eNew, proof? := proof } extraArgs
  else
    return none

def congr (e : Expr) : SimpM Result := do
  let f := e.getAppFn
  if f.isConst then
    let congrThms ← getSimpCongrTheorems
    let cs := congrThms.get f.constName!
    for c in cs do
      match (← trySimpCongrTheorem? c e) with
      | none   => pure ()
      | some r => return r
    congrDefault e
  else
    congrDefault e

def simpApp (e : Expr) : SimpM Result := do
  if isOfNatNatLit e || isOfScientificLit e || isCharLit e then
    -- Recall that we fold "orphan" kernel Nat literals `n` into `OfNat.ofNat n`
    return { expr := e }
  else
    congr e

def simpStep (e : Expr) : SimpM Result := do
  match e with
  | .mdata m e   => let r ← simp e; return { r with expr := mkMData m r.expr }
  | .proj ..     => simpProj e
  | .app ..      => simpApp e
  | .lam ..      => simpLambda e
  | .forallE ..  => simpForall e
  | .letE ..     => simpLet e
  | .const ..    => simpConst e
  | .bvar ..     => unreachable!
  | .sort ..     => return { expr := e }
  | .lit ..      => return { expr := e }
  | .mvar ..     => return { expr := (← instantiateMVars e) }
  | .fvar ..     => return { expr := (← reduceFVar (← getConfig) (← getSimpTheorems) e) }

def cacheResult (e : Expr) (cfg : Config) (r : Result) : SimpM Result := do
  if cfg.memoize && r.cache then
    modify fun s => { s with cache := s.cache.insert e r }
  return r

partial def simpLoop (e : Expr) : SimpM Result := withIncRecDepth do
  let cfg ← getConfig
  if cfg.memoize then
    let cache := (← get).cache
    if let some result := cache.find? e then
      return result
  if (← get).numSteps > cfg.maxSteps then
    throwError "`simp` failed: maximum number of steps exceeded"
  else
    checkSystem "simp"
    modify fun s => { s with numSteps := s.numSteps + 1 }
    match (← pre e) with
    | .done r  => cacheResult e cfg r
    | .visit r => cacheResult e cfg (← r.mkEqTrans (← simpLoop r.expr))
    | .continue none => visitPreContinue cfg { expr := e }
    | .continue (some r) => visitPreContinue cfg r
where
  visitPreContinue (cfg : Config) (r : Result) : SimpM Result := do
    let eNew ← reduceStep r.expr
    if eNew != r.expr then
      trace[Debug.Meta.Tactic.simp] "reduceStep (pre) {e} => {eNew}"
      let r := { r with expr := eNew }
      cacheResult e cfg (← r.mkEqTrans (← simpLoop r.expr))
    else
      let r ← r.mkEqTrans (← simpStep r.expr)
      visitPost cfg r
  visitPost (cfg : Config) (r : Result) : SimpM Result := do
    match (← post r.expr) with
    | .done r' => cacheResult e cfg (← r.mkEqTrans r')
    | .continue none => visitPostContinue cfg r
    | .visit r' | .continue (some r') => visitPostContinue cfg (← r.mkEqTrans r')
  visitPostContinue (cfg : Config) (r : Result) : SimpM Result := do
    let mut r := r
    unless cfg.singlePass || e == r.expr do
      r ← r.mkEqTrans (← simpLoop r.expr)
    cacheResult e cfg r

@[export lean_simp]
def simpImpl (e : Expr) : SimpM Result := withIncRecDepth do
  checkSystem "simp"
  if (← isProof e) then
    return { expr := e }
  trace[Meta.Tactic.simp.heads] "{repr e.toHeadIndex}"
  simpLoop e

@[inline] def withCatchingRuntimeEx (x : SimpM α) : SimpM α := do
  if (← getConfig).catchRuntime then
    tryCatchRuntimeEx x
      fun ex => do
        reportDiag (← get).diag
        if ex.isRuntime then
          throwNestedTacticEx `simp ex
        else
          throw ex
  else
    x

def mainCore (e : Expr) (ctx : Context) (s : State := {}) (methods : Methods := {}) : MetaM (Result × State) := do
  SimpM.run ctx s methods <| withCatchingRuntimeEx <| simp e

def main (e : Expr) (ctx : Context) (stats : Stats := {}) (methods : Methods := {}) : MetaM (Result × Stats) := do
  let (r, s) ← mainCore e ctx { stats with } methods
  return (r, { s with })

def dsimpMainCore (e : Expr) (ctx : Context) (s : State := {}) (methods : Methods := {}) : MetaM (Expr × State) := do
  SimpM.run ctx s methods <| withCatchingRuntimeEx <| dsimp e

def dsimpMain (e : Expr) (ctx : Context) (stats : Stats := {}) (methods : Methods := {}) : MetaM (Expr × Stats) := do
  let (r, s) ← dsimpMainCore e ctx { stats with } methods
  return (r, { s with })

end Simp
open Simp (SimprocsArray Stats)

def simpCore (e : Expr) (ctx : Simp.Context) (simprocs : SimprocsArray := #[]) (discharge? : Option Simp.Discharge := none)
    (s : Simp.State := {}) : MetaM (Simp.Result × Simp.State) := do profileitM Exception "simp" (← getOptions) do
  match discharge? with
  | none   => Simp.mainCore e ctx s (methods := Simp.mkDefaultMethodsCore simprocs)
  | some d => Simp.mainCore e ctx s (methods := Simp.mkMethods simprocs d (wellBehavedDischarge := false))

def simp (e : Expr) (ctx : Simp.Context) (simprocs : SimprocsArray := #[]) (discharge? : Option Simp.Discharge := none)
    (stats : Stats := {}) : MetaM (Simp.Result × Stats) := do profileitM Exception "simp" (← getOptions) do
  let (r, s) ← simpCore e ctx simprocs discharge? { stats with }
  return (r, { s with })

def dsimp (e : Expr) (ctx : Simp.Context) (simprocs : SimprocsArray := #[])
    (stats : Stats := {}) : MetaM (Expr × Stats) := do profileitM Exception "dsimp" (← getOptions) do
  Simp.dsimpMain e ctx stats (methods := Simp.mkDefaultMethodsCore simprocs )

/-- See `simpTarget`. This method assumes `mvarId` is not assigned, and we are already using `mvarId`s local context. -/
def simpTargetCore (mvarId : MVarId) (ctx : Simp.Context) (simprocs : SimprocsArray := #[]) (discharge? : Option Simp.Discharge := none)
    (mayCloseGoal := true) (stats : Stats := {}) : MetaM (Option MVarId × Stats) := do
  let target ← instantiateMVars (← mvarId.getType)
  let (r, stats) ← simp target ctx simprocs discharge? stats
  if mayCloseGoal && r.expr.isTrue then
    match r.proof? with
    | some proof => mvarId.assign (← mkOfEqTrue proof)
    | none => mvarId.assign (mkConst ``True.intro)
    return (none, stats)
  else
    return (← applySimpResultToTarget mvarId target r, stats)

/--
  Simplify the given goal target (aka type). Return `none` if the goal was closed. Return `some mvarId'` otherwise,
  where `mvarId'` is the simplified new goal. -/
def simpTarget (mvarId : MVarId) (ctx : Simp.Context) (simprocs : SimprocsArray := #[]) (discharge? : Option Simp.Discharge := none)
    (mayCloseGoal := true) (stats : Stats := {}) : MetaM (Option MVarId × Stats) :=
  mvarId.withContext do
    mvarId.checkNotAssigned `simp
    simpTargetCore mvarId ctx simprocs discharge? mayCloseGoal stats

/--
Applies the result `r` for `type` (which is inhabited by `val`). Returns `none` if the goal was closed. Returns `some (val', type')`
otherwise, where `val' : type'` and `type'` is the simplified `type`.

This method assumes `mvarId` is not assigned, and we are already using `mvarId`s local context. -/
def applySimpResult (mvarId : MVarId) (val : Expr) (type : Expr) (r : Simp.Result) (mayCloseGoal := true) : MetaM (Option (Expr × Expr)) := do
  if mayCloseGoal && r.expr.isFalse then
    match r.proof? with
    | some eqProof => mvarId.assign (← mkFalseElim (← mvarId.getType) (mkApp4 (mkConst ``Eq.mp [levelZero]) type r.expr eqProof val))
    | none => mvarId.assign (← mkFalseElim (← mvarId.getType) val)
    return none
  else
    match r.proof? with
    | some eqProof =>
      let u ← getLevel type
      return some (mkApp4 (mkConst ``Eq.mp [u]) type r.expr eqProof val, r.expr)
    | none =>
      if r.expr != type then
        return some ((← mkExpectedTypeHint val r.expr), r.expr)
      else
        return some (val, r.expr)

def applySimpResultToFVarId (mvarId : MVarId) (fvarId : FVarId) (r : Simp.Result) (mayCloseGoal : Bool) : MetaM (Option (Expr × Expr)) := do
  let localDecl ← fvarId.getDecl
  applySimpResult mvarId (mkFVar fvarId) localDecl.type r mayCloseGoal

/--
  Simplify `prop` (which is inhabited by `proof`). Return `none` if the goal was closed. Return `some (proof', prop')`
  otherwise, where `proof' : prop'` and `prop'` is the simplified `prop`.

  This method assumes `mvarId` is not assigned, and we are already using `mvarId`s local context. -/
def simpStep (mvarId : MVarId) (proof : Expr) (prop : Expr) (ctx : Simp.Context) (simprocs : SimprocsArray := #[]) (discharge? : Option Simp.Discharge := none)
    (mayCloseGoal := true) (stats : Stats := {}) : MetaM (Option (Expr × Expr) × Stats) := do
  let (r, stats) ← simp prop ctx simprocs discharge? stats
  return (← applySimpResult mvarId proof prop r (mayCloseGoal := mayCloseGoal), stats)

def applySimpResultToLocalDeclCore (mvarId : MVarId) (fvarId : FVarId) (r : Option (Expr × Expr)) : MetaM (Option (FVarId × MVarId)) := do
  match r with
  | none => return none
  | some (value, type') =>
    let localDecl ← fvarId.getDecl
    if localDecl.type != type' then
      let mvarId ← mvarId.assert localDecl.userName type' value
      let mvarId ← mvarId.tryClear localDecl.fvarId
      let (fvarId, mvarId) ← mvarId.intro1P
      return some (fvarId, mvarId)
    else
      return some (fvarId, mvarId)

/--
  Simplify `simp` result to the given local declaration. Return `none` if the goal was closed.
  This method assumes `mvarId` is not assigned, and we are already using `mvarId`s local context. -/
def applySimpResultToLocalDecl (mvarId : MVarId) (fvarId : FVarId) (r : Simp.Result) (mayCloseGoal : Bool) : MetaM (Option (FVarId × MVarId)) := do
  if r.proof?.isNone then
    -- New result is definitionally equal to input. Thus, we can avoid creating a new variable if there are dependencies
    let mvarId ← mvarId.replaceLocalDeclDefEq fvarId r.expr
    if mayCloseGoal && r.expr.isFalse then
      mvarId.assign (← mkFalseElim (← mvarId.getType) (mkFVar fvarId))
      return none
    else
      return some (fvarId, mvarId)
  else
    applySimpResultToLocalDeclCore mvarId fvarId (← applySimpResultToFVarId mvarId fvarId r mayCloseGoal)

def simpLocalDecl (mvarId : MVarId) (fvarId : FVarId) (ctx : Simp.Context) (simprocs : SimprocsArray := #[]) (discharge? : Option Simp.Discharge := none)
    (mayCloseGoal := true) (stats : Stats := {}) : MetaM (Option (FVarId × MVarId) × Stats) := do
  mvarId.withContext do
    mvarId.checkNotAssigned `simp
    let type ← instantiateMVars (← fvarId.getType)
    let (r, stats) ← simpStep mvarId (mkFVar fvarId) type ctx simprocs discharge? mayCloseGoal stats
    return (← applySimpResultToLocalDeclCore mvarId fvarId r, stats)

def simpGoal (mvarId : MVarId) (ctx : Simp.Context) (simprocs : SimprocsArray := #[]) (discharge? : Option Simp.Discharge := none)
    (simplifyTarget : Bool := true) (fvarIdsToSimp : Array FVarId := #[])
    (stats : Stats := {}) : MetaM (Option (Array FVarId × MVarId) × Stats) := do
  mvarId.withContext do
    mvarId.checkNotAssigned `simp
    let mut mvarIdNew := mvarId
    let mut toAssert := #[]
    let mut replaced := #[]
    let mut stats := stats
    for fvarId in fvarIdsToSimp do
      let localDecl ← fvarId.getDecl
      let type ← instantiateMVars localDecl.type
      let ctx := ctx.setSimpTheorems <| ctx.simpTheorems.eraseTheorem (.fvar localDecl.fvarId)
      let (r, stats') ← simp type ctx simprocs discharge? stats
      stats := stats'
      match r.proof? with
      | some _ => match (← applySimpResult mvarIdNew (mkFVar fvarId) type r) with
        | none => return (none, stats)
        | some (value, type) => toAssert := toAssert.push { userName := localDecl.userName, type := type, value := value }
      | none =>
        if r.expr.isFalse then
          mvarIdNew.assign (← mkFalseElim (← mvarIdNew.getType) (mkFVar fvarId))
          return (none, stats)
        -- TODO: if there are no forwards dependencies we may consider using the same approach we used when `r.proof?` is a `some ...`
        -- Reason: it introduces a `mkExpectedTypeHint`
        mvarIdNew ← mvarIdNew.replaceLocalDeclDefEq fvarId r.expr
        replaced := replaced.push fvarId
    if simplifyTarget then
      match (← simpTarget mvarIdNew ctx simprocs discharge? (stats := stats)) with
      | (none, stats') => return (none, stats')
      | (some mvarIdNew', stats') => mvarIdNew := mvarIdNew'; stats := stats'
    let (fvarIdsNew, mvarIdNew') ← mvarIdNew.assertHypotheses toAssert
    mvarIdNew := mvarIdNew'
    let toClear := fvarIdsToSimp.filter fun fvarId => !replaced.contains fvarId
    mvarIdNew ← mvarIdNew.tryClearMany toClear
    if ctx.config.failIfUnchanged && mvarId == mvarIdNew then
      throwError "`simp` made no progress"
    return (some (fvarIdsNew, mvarIdNew), stats)

def simpTargetStar (mvarId : MVarId) (ctx : Simp.Context) (simprocs : SimprocsArray := #[]) (discharge? : Option Simp.Discharge := none)
    (stats : Stats := {}) : MetaM (TacticResultCNM × Stats) := mvarId.withContext do
  let mut ctx := ctx
  for h in (← getPropHyps) do
    let localDecl ← h.getDecl
    let proof  := localDecl.toExpr
    let simpTheorems ← ctx.simpTheorems.addTheorem (.fvar h) proof (config := ctx.indexConfig)
    ctx := ctx.setSimpTheorems simpTheorems
  match (← simpTarget mvarId ctx simprocs discharge? (stats := stats)) with
  | (none, stats) => return (TacticResultCNM.closed, stats)
  | (some mvarId', stats') =>
    if (← mvarId.getType) == (← mvarId'.getType) then
      return (TacticResultCNM.noChange, stats)
    else
      return (TacticResultCNM.modified mvarId', stats')

def dsimpGoal (mvarId : MVarId) (ctx : Simp.Context) (simprocs : SimprocsArray := #[]) (simplifyTarget : Bool := true) (fvarIdsToSimp : Array FVarId := #[])
    (stats : Stats := {}) : MetaM (Option MVarId × Stats) := do
   mvarId.withContext do
    mvarId.checkNotAssigned `simp
    let mut mvarIdNew := mvarId
    let mut stats : Stats := stats
    for fvarId in fvarIdsToSimp do
      let type ← instantiateMVars (← fvarId.getType)
      let (typeNew, stats') ← dsimp type ctx simprocs
      stats := stats'
      if typeNew.isFalse then
        mvarIdNew.assign (← mkFalseElim (← mvarIdNew.getType) (mkFVar fvarId))
        return (none, stats)
      if typeNew != type then
        mvarIdNew ← mvarIdNew.replaceLocalDeclDefEq fvarId typeNew
    if simplifyTarget then
      let target ← mvarIdNew.getType
      let (targetNew, stats') ← dsimp target ctx simprocs stats
      stats := stats'
      if targetNew.isTrue then
        mvarIdNew.assign (mkConst ``True.intro)
        return (none, stats)
      if let some (_, lhs, rhs) := targetNew.consumeMData.eq? then
        if (← withReducible <| isDefEq lhs rhs) then
          mvarIdNew.assign (← mkEqRefl lhs)
          return (none, stats)
      if target != targetNew then
        mvarIdNew ← mvarIdNew.replaceTargetDefEq targetNew
      pure () -- FIXME: bug in do notation if this is removed?
    if ctx.config.failIfUnchanged && mvarId == mvarIdNew then
      throwError "`dsimp` made no progress"
    return (some mvarIdNew, stats)

end Lean.Meta
