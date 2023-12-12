/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Meta.Offset
import Lean.Meta.UnificationHint
import Lean.Util.OccursCheck

namespace Lean.Meta

/--
  Return `true` if `e` is of the form `fun (x_1 ... x_n) => ?m y_1 ... y_k)`, and `?m` is unassigned.
  Remark: `n`, `k` may be 0.
  This function is used to filter unification problems in
  `isDefEqArgs`/`isDefEqEtaStruct` where we can assign proofs.
  If one side is of the form described above, then we can likely assign `?m`.
  But it it's not, we would most likely apply proof irrelevance, which is
  usually very expensive since it needs to unify the types as well.
-/
def isAbstractedUnassignedMVar : Expr → MetaM Bool
  | .lam _ _ b _ => isAbstractedUnassignedMVar b
  | .app a _ => isAbstractedUnassignedMVar a
  | .mvar mvarId => do
    if (← mvarId.isReadOnlyOrSyntheticOpaque) then
      pure false
    else if (← mvarId.isAssigned) then
      pure false
    else
      pure true
  | _ => pure false

/--
  Return true if `b` is of the form `mk a.1 ... a.n`, and `a` is not a constructor application.

  If `a` and `b` are constructor applications, the method returns `false` to force `isDefEq` to use `isDefEqArgs`.
  For example, suppose we are trying to solve the constraint
  ```
  Fin.mk ?n ?h =?= Fin.mk n h
  ```
  If this method is applied, the constraints are reduced to
  ```
  n =?= (Fin.mk ?n ?h).1
  h =?= (Fin.mk ?n ?h).2
  ```
  The first constraint produces the assignment `?n := n`. Then, the second constraint is solved using proof irrelevance without
  assigning `?h`.
  TODO: investigate better solutions for the proof irrelevance issue. The problem above can happen is other scenarios.
  That is, proof irrelevance may prevent us from performing desired mvar assignments.
-/
private def isDefEqEtaStruct (a b : Expr) : MetaM Bool := do
  matchConstCtor b.getAppFn (fun _ => return false) fun ctorVal us => do
    if (← useEtaStruct ctorVal.induct) then
      matchConstCtor a.getAppFn (fun _ => go ctorVal us) fun _ _ => return false
    else
      return false
where
  go ctorVal us := do
    if ctorVal.numParams + ctorVal.numFields != b.getAppNumArgs then
      trace[Meta.isDefEq.eta.struct] "failed, insufficient number of arguments at{indentExpr b}"
      return false
    else
      if !isStructureLike (← getEnv) ctorVal.induct then
        trace[Meta.isDefEq.eta.struct] "failed, type is not a structure{indentExpr b}"
        return false
      else if (← isDefEq (← inferType a) (← inferType b)) then
        checkpointDefEq do
          let args := b.getAppArgs
          let params := args[:ctorVal.numParams].toArray
          for i in [ctorVal.numParams : args.size] do
            let j := i - ctorVal.numParams
            let proj ← mkProjFn ctorVal us params j a
            if ← isProof proj then
              unless ← isAbstractedUnassignedMVar args[i]! do
                -- Skip expensive unification problem that is likely solved
                -- using proof irrelevance.  We already know that `proj` and
                -- `args[i]!` have the same type, so they're defeq in any case.
                -- See comment at `isAbstractedUnassignedMVar`.
                continue
            trace[Meta.isDefEq.eta.struct] "{a} =?= {b} @ [{j}], {proj} =?= {args[i]!}"
            unless (← isDefEq proj args[i]!) do
              trace[Meta.isDefEq.eta.struct] "failed, unexpect arg #{i}, projection{indentExpr proj}\nis not defeq to{indentExpr args[i]!}"
              return false
          return true
      else
        return false

/--
  Try to solve `a := (fun x => t) =?= b` by eta-expanding `b`,
  resulting in `t =?= b x` (with a fresh free variable `x`).

  Remark: eta-reduction is not a good alternative even in a system without universe cumulativity like Lean.
  Example:
    ```
    (fun x : A => f ?m) =?= f
    ```
    The left-hand side of the constraint above it not eta-reduced because `?m` is a metavariable.

  Note: we do not backtrack after applying η-expansion anymore.
  There is no case where `(fun x => t) =?= b` unifies, but `t =?= b x` does not.
  Backtracking after η-expansion results in lots of duplicate δ-reductions,
  because we can δ-reduce `a` before and after the η-expansion.
  The fresh free variable `x` also busts the cache.
  See https://github.com/leanprover/lean4/pull/2002 -/
private def isDefEqEta (a b : Expr) : MetaM LBool := do
  if a.isLambda && !b.isLambda then
    let bType ← inferType b
    let bType ← whnfD bType
    match bType with
    | Expr.forallE n d _ c =>
      let b' := mkLambda n c d (mkApp b (mkBVar 0))
      toLBoolM <| checkpointDefEq <| Meta.isExprDefEqAux a b'
    | _ => return .undef
  else
    return .undef

/-- Support for `Lean.reduceBool` and `Lean.reduceNat` -/
def isDefEqNative (s t : Expr) : MetaM LBool := do
  let isDefEq (s t) : MetaM LBool := toLBoolM <| Meta.isExprDefEqAux s t
  let s? ← reduceNative? s
  let t? ← reduceNative? t
  match s?, t? with
  | some s, some t => isDefEq s t
  | some s, none   => isDefEq s t
  | none,   some t => isDefEq s t
  | none,   none   => pure LBool.undef

/-- Support for reducing Nat basic operations. -/
def isDefEqNat (s t : Expr) : MetaM LBool := do
  let isDefEq (s t) : MetaM LBool := toLBoolM <| Meta.isExprDefEqAux s t
  if s.hasFVar || s.hasMVar || t.hasFVar || t.hasMVar then
    pure LBool.undef
  else
    let s? ← reduceNat? s
    let t? ← reduceNat? t
    match s?, t? with
    | some s, some t => isDefEq s t
    | some s, none   => isDefEq s t
    | none,   some t => isDefEq s t
    | none,   none   => pure LBool.undef

/-- Support for constraints of the form `("..." =?= String.mk cs)` -/
def isDefEqStringLit (s t : Expr) : MetaM LBool := do
  let isDefEq (s t) : MetaM LBool := toLBoolM <| Meta.isExprDefEqAux s t
  if s.isStringLit && t.isAppOf ``String.mk then
    isDefEq s.toCtorIfLit t
  else if s.isAppOf `String.mk && t.isStringLit then
    isDefEq s t.toCtorIfLit
  else
    pure LBool.undef

/--
  Return `true` if `e` is of the form `fun (x_1 ... x_n) => ?m x_1 ... x_n)`, and `?m` is unassigned.
  Remark: `n` may be 0. -/
def isEtaUnassignedMVar (e : Expr) : MetaM Bool := do
  match e.etaExpanded? with
  | some (Expr.mvar mvarId) =>
    if (← mvarId.isReadOnlyOrSyntheticOpaque) then
      pure false
    else if (← mvarId.isAssigned) then
      pure false
    else
      pure true
  | _   => pure false

private def trySynthPending (e : Expr) : MetaM Bool := do
  let mvarId? ← getStuckMVar? e
  match mvarId? with
  | some mvarId => Meta.synthPending mvarId
  | none        => pure false

/--
  Result type for `isDefEqArgsFirstPass`.
-/
inductive DefEqArgsFirstPassResult where
  /--
  Failed to establish that explicit arguments are def-eq.
  Remark: higher output parameters, and parameters that depend on them
  are postponed.
  -/
  | failed
  /--
  Succeeded. The array `postponedImplicit` contains the position
  of the implicit arguments for which def-eq has been postponed.
  `postponedHO` contains the higher order output parameters, and parameters
  that depend on them. They should be processed after the implicit ones.
  `postponedHO` is used to handle applications involving functions that
  contain higher order output parameters. Example:
  ```lean
  getElem :
    {cont : Type u_1} → {idx : Type u_2} → {elem : Type u_3} →
    {dom : cont → idx → Prop} → [self : GetElem cont idx elem dom] →
    (xs : cont) → (i : idx) → (h : dom xs i) → elem
  ```
  The arguments `dom` and `h` must be processed after all implicit arguments
  otherwise higher-order unification problems are generated. See issue #1299,
  when trying to solve
  ```
  getElem ?a ?i ?h =?= getElem a i (Fin.val_lt_of_le i ...)
  ```
  we have to solve the constraint
  ```
  ?dom a i.val =?= LT.lt i.val (Array.size a)
  ```
  by solving after the instance has been synthesized, we reduce this constraint to
  a simple check.
  -/
  | ok (postponedImplicit : Array Nat) (postponedHO : Array Nat)

/--
  First pass for `isDefEqArgs`. We unify explicit arguments, *and* easy cases
  Here, we say a case is easy if it is of the form

       ?m =?= t
       or
       t  =?= ?m

  where `?m` is unassigned.

  These easy cases are not just an optimization. When
  `?m` is a function, by assigning it to t, we make sure
  a unification constraint (in the explicit part)
  ```
  ?m t =?= f s
  ```
  is not higher-order.

  We also handle the eta-expanded cases:
  ```
  fun x₁ ... xₙ => ?m x₁ ... xₙ =?= t
  t =?= fun x₁ ... xₙ => ?m x₁ ... xₙ
  ```
  This is important because type inference often produces
  eta-expanded terms, and without this extra case, we could
  introduce counter intuitive behavior.

  Pre: `paramInfo.size <= args₁.size = args₂.size`

  See `DefEqArgsFirstPassResult` for additional information.
-/
private def isDefEqArgsFirstPass
    (paramInfo : Array ParamInfo) (args₁ args₂ : Array Expr) : MetaM DefEqArgsFirstPassResult := do
  let mut postponedImplicit := #[]
  let mut postponedHO := #[]
  for i in [:paramInfo.size] do
    let info := paramInfo[i]!
    let a₁ := args₁[i]!
    let a₂ := args₂[i]!
    if info.dependsOnHigherOrderOutParam || info.higherOrderOutParam then
      trace[Meta.isDefEq] "found messy {a₁} =?= {a₂}"
      postponedHO := postponedHO.push i
    else if info.isExplicit then
      if info.isProp then
        unless ← isAbstractedUnassignedMVar a₁ <||> isAbstractedUnassignedMVar a₂ do
          -- Skip expensive unification problem that is likely solved
          -- using proof irrelevance.  We already know that `a₁` and
          -- `a₂` have the same type, so they're defeq in any case.
          -- See comment at `isAbstractedUnassignedMVar`.
          continue
      unless (← Meta.isExprDefEqAux a₁ a₂) do
        return .failed
    else if (← isEtaUnassignedMVar a₁ <||> isEtaUnassignedMVar a₂) then
      unless (← Meta.isExprDefEqAux a₁ a₂) do
        return .failed
    else
      if info.isProp then
        unless ← isAbstractedUnassignedMVar a₁ <||> isAbstractedUnassignedMVar a₂ do
          -- Skip expensive unification problem that is likely solved
          -- using proof irrelevance.  We already know that `a₁` and
          -- `a₂` have the same type, so they're defeq in any case.
          -- See comment at `isAbstractedUnassignedMVar`.
          continue
      postponedImplicit := postponedImplicit.push i
  return .ok postponedImplicit postponedHO

private partial def isDefEqArgs (f : Expr) (args₁ args₂ : Array Expr) : MetaM Bool := do
  unless args₁.size == args₂.size do return false
  let finfo ← getFunInfoNArgs f args₁.size
  let .ok postponedImplicit postponedHO ← isDefEqArgsFirstPass finfo.paramInfo args₁ args₂ | pure false
  -- finfo.paramInfo.size may be smaller than args₁.size
  for i in [finfo.paramInfo.size:args₁.size] do
    unless (← Meta.isExprDefEqAux args₁[i]! args₂[i]!) do
      return false
  for i in postponedImplicit do
    /- Second pass: unify implicit arguments.
       In the second pass, we make sure we are unfolding at
       least non reducible definitions (default setting). -/
    let a₁   := args₁[i]!
    let a₂   := args₂[i]!
    let info := finfo.paramInfo[i]!
    if info.isInstImplicit then
      discard <| trySynthPending a₁
      discard <| trySynthPending a₂
    unless (← withAtLeastTransparency TransparencyMode.default <| Meta.isExprDefEqAux a₁ a₂) do
      return false
  for i in postponedHO do
    let a₁   := args₁[i]!
    let a₂   := args₂[i]!
    let info := finfo.paramInfo[i]!
    if info.isInstImplicit then
      unless (← withAtLeastTransparency TransparencyMode.default <| Meta.isExprDefEqAux a₁ a₂) do
       return false
    else
      unless (← Meta.isExprDefEqAux a₁ a₂) do
        return false
  return true

/--
  Check whether the types of the free variables at `fvars` are
  definitionally equal to the types at `ds₂`.

  Pre: `fvars.size == ds₂.size`

  This method also updates the set of local instances, and invokes
  the continuation `k` with the updated set.

  We can't use `withNewLocalInstances` because the `isDeq fvarType d₂`
  may use local instances. -/
@[specialize] partial def isDefEqBindingDomain (fvars : Array Expr) (ds₂ : Array Expr) (k : MetaM Bool) : MetaM Bool :=
  let rec loop (i : Nat) := do
    if h : i < fvars.size then do
      let fvar := fvars.get ⟨i, h⟩
      let fvarDecl ← getFVarLocalDecl fvar
      let fvarType := fvarDecl.type
      let d₂       := ds₂[i]!
      if (← Meta.isExprDefEqAux fvarType d₂) then
        match (← isClass? fvarType) with
        | some className => withNewLocalInstance className fvar <| loop (i+1)
        | none           => loop (i+1)
      else
        pure false
    else
      k
  loop 0

/-- Auxiliary function for `isDefEqBinding` for handling binders `forall/fun`.
   It accumulates the new free variables in `fvars`, and declare them at `lctx`.
   We use the domain types of `e₁` to create the new free variables.
   We store the domain types of `e₂` at `ds₂`. -/
private partial def isDefEqBindingAux (lctx : LocalContext) (fvars : Array Expr) (e₁ e₂ : Expr) (ds₂ : Array Expr) : MetaM Bool :=
  let process (n : Name) (d₁ d₂ b₁ b₂ : Expr) : MetaM Bool := do
    let d₁     := d₁.instantiateRev fvars
    let d₂     := d₂.instantiateRev fvars
    let fvarId ← mkFreshFVarId
    let lctx   := lctx.mkLocalDecl fvarId n d₁
    let fvars  := fvars.push (mkFVar fvarId)
    isDefEqBindingAux lctx fvars b₁ b₂ (ds₂.push d₂)
  match e₁, e₂ with
  | Expr.forallE n d₁ b₁ _, Expr.forallE _ d₂ b₂ _ => process n d₁ d₂ b₁ b₂
  | Expr.lam     n d₁ b₁ _, Expr.lam     _ d₂ b₂ _ => process n d₁ d₂ b₁ b₂
  | _,                      _                      =>
    withReader (fun ctx => { ctx with lctx := lctx }) do
      isDefEqBindingDomain fvars ds₂ do
        Meta.isExprDefEqAux (e₁.instantiateRev fvars) (e₂.instantiateRev fvars)

@[inline] private def isDefEqBinding (a b : Expr) : MetaM Bool := do
  let lctx ← getLCtx
  isDefEqBindingAux lctx #[] a b #[]

private def checkTypesAndAssign (mvar : Expr) (v : Expr) : MetaM Bool :=
  withTraceNodeBefore `Meta.isDefEq.assign.checkTypes (return m!"({mvar} : {← inferType mvar}) := ({v} : {← inferType v})") do
    if !mvar.isMVar then
      trace[Meta.isDefEq.assign.checkTypes] "metavariable expected"
      return false
    else
      -- must check whether types are definitionally equal or not, before assigning and returning true
      let mvarType ← inferType mvar
      let vType ← inferType v
      if (← withTransparency TransparencyMode.default <| Meta.isExprDefEqAux mvarType vType) then
        mvar.mvarId!.assign v
        pure true
      else
        pure false

/--
  Auxiliary method for solving constraints of the form `?m xs := v`.
  It creates a lambda using `mkLambdaFVars ys v`, where `ys` is a superset of `xs`.
  `ys` is often equal to `xs`. It is a bigger when there are let-declaration dependencies in `xs`.
  For example, suppose we have `xs` of the form `#[a, c]` where
  ```
  a : Nat
  b : Nat := f a
  c : b = a
  ```
  In this scenario, the type of `?m` is `(x1 : Nat) -> (x2 : f x1 = x1) -> C[x1, x2]`,
  and type of `v` is `C[a, c]`. Note that, `?m a c` is type correct since `f a = a` is definitionally equal
  to the type of `c : b = a`, and the type of `?m a c` is equal to the type of `v`.
  Note that `fun xs => v` is the term `fun (x1 : Nat) (x2 : b = x1) => v` which has type
  `(x1 : Nat) -> (x2 : b = x1) -> C[x1, x2]` which is not definitionally equal to the type of `?m`,
  and may not even be type correct.
  The issue here is that we are not capturing the `let`-declarations.

  This method collects let-declarations `y` occurring between `xs[0]` and `xs.back` s.t.
  some `x` in `xs` depends on `y`.
  `ys` is the `xs` with these extra let-declarations included.

  In the example above, `ys` is `#[a, b, c]`, and `mkLambdaFVars ys v` produces
  `fun a => let b := f a; fun (c : b = a) => v` which has a type definitionally equal to the type of `?m`.

  Recall that the method `checkAssignment` ensures `v` does not contain offending `let`-declarations.

  This method assumes that for any `xs[i]` and `xs[j]` where `i < j`, we have that `index of xs[i]` < `index of xs[j]`.
  where the index is the position in the local context.
-/
private partial def mkLambdaFVarsWithLetDeps (xs : Array Expr) (v : Expr) : MetaM (Option Expr) := do
  if not (← hasLetDeclsInBetween) then
    mkLambdaFVars xs v
  else
    let ys ← addLetDeps
    mkLambdaFVars ys v

where
  /-- Return true if there are let-declarions between `xs[0]` and `xs[xs.size-1]`.
     We use it a quick-check to avoid the more expensive collection procedure. -/
  hasLetDeclsInBetween : MetaM Bool := do
    let check (lctx : LocalContext) : Bool := Id.run do
      let start := lctx.getFVar! xs[0]! |>.index
      let stop  := lctx.getFVar! xs.back |>.index
      for i in [start+1:stop] do
        match lctx.getAt? i with
        | some localDecl =>
          if localDecl.isLet then
            return true
        | _ => pure ()
      return false
    if xs.size <= 1 then
      return false
    else
      return check (← getLCtx)

  /-- Traverse `e` and stores in the state `NameHashSet` any let-declaration with index greater than `(← read)`.
     The context `Nat` is the position of `xs[0]` in the local context. -/
  collectLetDeclsFrom (e : Expr) : ReaderT Nat (StateRefT FVarIdHashSet MetaM) Unit := do
    let rec visit (e : Expr) : MonadCacheT Expr Unit (ReaderT Nat (StateRefT FVarIdHashSet MetaM)) Unit :=
      checkCache e fun _ => do
        match e with
        | Expr.forallE _ d b _   => visit d; visit b
        | Expr.lam _ d b _       => visit d; visit b
        | Expr.letE _ t v b _    => visit t; visit v; visit b
        | Expr.app f a           => visit f; visit a
        | Expr.mdata _ b         => visit b
        | Expr.proj _ _ b        => visit b
        | Expr.fvar fvarId       =>
          let localDecl ← fvarId.getDecl
          if localDecl.isLet && localDecl.index > (← read) then
            modify fun s => s.insert localDecl.fvarId
        | _ => pure ()
    visit (← instantiateMVars e) |>.run

  /--
    Auxiliary definition for traversing all declarations between `xs[0]` ... `xs.back` backwards.
    The `Nat` argument is the current position in the local context being visited, and it is less than
    or equal to the position of `xs.back` in the local context.
    The `Nat` context `(← read)` is the position of `xs[0]` in the local context.
  -/
  collectLetDepsAux : Nat → ReaderT Nat (StateRefT FVarIdHashSet MetaM) Unit
    | 0   => return ()
    | i+1 => do
      if i+1 == (← read) then
        return ()
      else
        match (← getLCtx).getAt? (i+1) with
        | none => collectLetDepsAux i
        | some localDecl =>
          if (← get).contains localDecl.fvarId then
            collectLetDeclsFrom localDecl.type
            match localDecl.value? with
            | some val => collectLetDeclsFrom val
            | _ =>  pure ()
          collectLetDepsAux i

  /-- Computes the set `ys`. It is a set of `FVarId`s, -/
  collectLetDeps : MetaM FVarIdHashSet := do
    let lctx ← getLCtx
    let start := lctx.getFVar! xs[0]! |>.index
    let stop  := lctx.getFVar! xs.back |>.index
    let s := xs.foldl (init := {}) fun s x => s.insert x.fvarId!
    let (_, s) ← collectLetDepsAux stop |>.run start |>.run s
    return s

  /-- Computes the array `ys` containing let-decls between `xs[0]` and `xs.back` that
     some `x` in `xs` depends on. -/
  addLetDeps : MetaM (Array Expr) := do
    let lctx ← getLCtx
    let s ← collectLetDeps
    /- Convert `s` into the array `ys` -/
    let start := lctx.getFVar! xs[0]! |>.index
    let stop  := lctx.getFVar! xs.back |>.index
    let mut ys := #[]
    for i in [start:stop+1] do
      match lctx.getAt? i with
      | none => pure ()
      | some localDecl =>
        if s.contains localDecl.fvarId then
          ys := ys.push localDecl.toExpr
    return ys

/-!
  Each metavariable is declared in a particular local context.
  We use the notation `C |- ?m : t` to denote a metavariable `?m` that
  was declared at the local context `C` with type `t` (see `MetavarDecl`).
  We also use `?m@C` as a shorthand for `C |- ?m : t` where `t` is the type of `?m`.

  The following method process the unification constraint

       ?m@C a₁ ... aₙ =?= t

  We say the unification constraint is a pattern IFF

    1) `a₁ ... aₙ` are pairwise distinct free variables that are ​*not*​ let-variables.
    2) `a₁ ... aₙ` are not in `C`
    3) `t` only contains free variables in `C` and/or `{a₁, ..., aₙ}`
    4) For every metavariable `?m'@C'` occurring in `t`, `C'` is a subprefix of `C`
    5) `?m` does not occur in `t`

  Claim: we don't have to check free variable declarations. That is,
  if `t` contains a reference to `x : A := v`, we don't need to check `v`.
  Reason: The reference to `x` is a free variable, and it must be in `C` (by 1 and 3).
  If `x` is in `C`, then any metavariable occurring in `v` must have been defined in a strict subprefix of `C`.
  So, condition 4 and 5 are satisfied.

  If the conditions above have been satisfied, then the
  solution for the unification constrain is

    ?m := fun a₁ ... aₙ => t

  Now, we consider some workarounds/approximations.

 A1) Suppose `t` contains a reference to `x : A := v` and `x` is not in `C` (failed condition 3)
     (precise) solution: unfold `x` in `t`.

 A2) Suppose some `aᵢ` is in `C` (failed condition 2)
     (approximated) solution (when `config.quasiPatternApprox` is set to true) :
     ignore condition and also use

        ?m := fun a₁ ... aₙ => t

   Here is an example where this approximation fails:
   Given `C` containing `a : nat`, consider the following two constraints
         ?m@C a =?= a
         ?m@C b =?= a

   If we use the approximation in the first constraint, we get
         ?m := fun x => x
   when we apply this solution to the second one we get a failure.

   IMPORTANT: When applying this approximation we need to make sure the
   abstracted term `fun a₁ ... aₙ => t` is type correct. The check
   can only be skipped in the pattern case described above. Consider
   the following example. Given the local context

      (α : Type) (a : α)

   we try to solve

     ?m α =?= @id α a

   If we use the approximation above we obtain:

     ?m := (fun α' => @id α' a)

   which is a type incorrect term. `a` has type `α` but it is expected to have
   type `α'`.

   The problem occurs because the right hand side contains a free variable
   `a` that depends on the free variable `α` being abstracted. Note that
   this dependency cannot occur in patterns.

   We can address this by type checking
   the term after abstraction. This is not a significant performance
   bottleneck because this case doesn't happen very often in practice
   (262 times when compiling stdlib on Jan 2018). The second example
   is trickier, but it also occurs less frequently (8 times when compiling
   stdlib on Jan 2018, and all occurrences were at Init/Control when
   we define monads and auxiliary combinators for them).
   We considered three options for the addressing the issue on the second example:

 A3) `a₁ ... aₙ` are not pairwise distinct (failed condition 1).
   In Lean3, we would try to approximate this case using an approach similar to A2.
   However, this approximation complicates the code, and is never used in the
   Lean3 stdlib and mathlib.

 A4) `t` contains a metavariable `?m'@C'` where `C'` is not a subprefix of `C`.
   If `?m'` is assigned, we substitute.
   If not, we create an auxiliary metavariable with a smaller scope.
   Actually, we let `elimMVarDeps` at `MetavarContext.lean` to perform this step.

 A5) If some `aᵢ` is not a free variable,
     then we use first-order unification (if `config.foApprox` is set to true)

       ?m a_1 ... a_i a_{i+1} ... a_{i+k} =?= f b_1 ... b_k

   reduces to

       ?M a_1 ... a_i =?= f
       a_{i+1}        =?= b_1
       ...
       a_{i+k}        =?= b_k


 A6) If (m =?= v) is of the form

        ?m a_1 ... a_n =?= ?m b_1 ... b_k

     then we use first-order unification (if `config.foApprox` is set to true)

 A7) When `foApprox`, we may use another approximation (`constApprox`) for solving constraints of the form
     ```
     ?m s₁ ... sₙ =?= t
     ```
     where `s₁ ... sₙ` are arbitrary terms. We solve them by assigning the constant function to `?m`.
     ```
     ?m := fun _ ... _ => t
     ```

     In general, this approximation may produce bad solutions, and may prevent coercions from being tried.
     For example, consider the term `pure (x > 0)` with inferred type `?m Prop` and expected type `IO Bool`.
     In this situation, the
     elaborator generates the unification constraint
     ```
     ?m Prop =?= IO Bool
     ```
     It is not a higher-order pattern, nor first-order approximation is applicable. However, constant approximation
     produces the bogus solution `?m := fun _ => IO Bool`, and prevents the system from using the coercion from
     the decidable proposition `x > 0` to `Bool`.

     On the other hand, the constant approximation is desirable for elaborating the term
     ```
     let f (x : _) := pure "hello"; f ()
     ```
     with expected type `IO String`.
     In this example, the following unification constraint is generated.
     ```
     ?m () String =?= IO String
     ```
     It is not a higher-order pattern, first-order approximation reduces it to
     ```
     ?m () =?= IO
     ```
     which fails to be solved. However, constant approximation solves it by assigning
     ```
     ?m := fun _ => IO
     ```
     Note that `f`s type is `(x : ?α) -> ?m x String`. The metavariable `?m` may depend on `x`.
     If `constApprox` is set to true, we use constant approximation. Otherwise, we use a heuristic to decide
     whether we should apply it or not. The heuristic is based on observing where the constraints above come from.
     In the first example, the constraint `?m Prop =?= IO Bool` come from polymorphic method where `?m` is expected to
     be a **function** of type `Type -> Type`. In the second example, the first argument of `?m` is used to model
     a **potential** dependency on `x`. By using constant approximation here, we are just saying the type of `f`
     does **not** depend on `x`. We claim this is a reasonable approximation in practice. Moreover, it is expected
     by any functional programmer used to non-dependently type languages (e.g., Haskell).
     We distinguish the two cases above by using the field `numScopeArgs` at `MetavarDecl`. This field tracks
     how many metavariable arguments are representing dependencies.
-/

def mkAuxMVar (lctx : LocalContext) (localInsts : LocalInstances) (type : Expr) (numScopeArgs : Nat := 0) : MetaM Expr := do
  mkFreshExprMVarAt lctx localInsts type MetavarKind.natural Name.anonymous numScopeArgs

namespace CheckAssignment

builtin_initialize checkAssignmentExceptionId : InternalExceptionId ← registerInternalExceptionId `checkAssignment
builtin_initialize outOfScopeExceptionId : InternalExceptionId ← registerInternalExceptionId `outOfScope

structure State where
  cache : ExprStructMap Expr := {}

structure Context where
  mvarId        : MVarId
  mvarDecl      : MetavarDecl
  fvars         : Array Expr
  hasCtxLocals  : Bool
  rhs           : Expr

abbrev CheckAssignmentM := ReaderT Context $ StateRefT State MetaM

def throwCheckAssignmentFailure : CheckAssignmentM α :=
  throw <| Exception.internal checkAssignmentExceptionId

def throwOutOfScopeFVar : CheckAssignmentM α :=
  throw <| Exception.internal outOfScopeExceptionId

private def findCached? (e : Expr) : CheckAssignmentM (Option Expr) := do
  return (← get).cache.find? e

private def cache (e r : Expr) : CheckAssignmentM Unit := do
  modify fun s => { s with cache := s.cache.insert e r }

instance : MonadCache Expr Expr CheckAssignmentM where
  findCached? := findCached?
  cache       := cache

private def addAssignmentInfo (msg : MessageData) : CheckAssignmentM MessageData := do
  let ctx ← read
  return m!"{msg} @ {mkMVar ctx.mvarId} {ctx.fvars} := {ctx.rhs}"

@[inline] def run (x : CheckAssignmentM Expr) (mvarId : MVarId) (fvars : Array Expr) (hasCtxLocals : Bool) (v : Expr) : MetaM (Option Expr) := do
  let mvarDecl ← mvarId.getDecl
  let ctx := { mvarId := mvarId, mvarDecl := mvarDecl, fvars := fvars, hasCtxLocals := hasCtxLocals, rhs := v : Context }
  let x : CheckAssignmentM (Option Expr) :=
    catchInternalIds [outOfScopeExceptionId, checkAssignmentExceptionId]
      (do let e ← x; return some e)
      (fun _ => pure none)
  x.run ctx |>.run' {}

mutual

  partial def checkFVar (fvar : Expr) : CheckAssignmentM Expr := do
    let ctxMeta ← readThe Meta.Context
    let ctx ← read
    if ctx.mvarDecl.lctx.containsFVar fvar then
      pure fvar
    else
      let lctx := ctxMeta.lctx
      match lctx.findFVar? fvar with
      | some (.ldecl (value := v) ..) => check v
      | _ =>
        if ctx.fvars.contains fvar then pure fvar
        else
          traceM `Meta.isDefEq.assign.outOfScopeFVar do addAssignmentInfo fvar
          throwOutOfScopeFVar

  partial def checkMVar (mvar : Expr) : CheckAssignmentM Expr := do
    let mvarId := mvar.mvarId!
    let ctx  ← read
    if mvarId == ctx.mvarId then
      traceM `Meta.isDefEq.assign.occursCheck <| addAssignmentInfo "occurs check failed"
      throwCheckAssignmentFailure
    else match (← getExprMVarAssignment? mvarId) with
      | some v => check v
      | none   =>
        match (← mvarId.findDecl?) with
        | none          => throwUnknownMVar mvarId
        | some mvarDecl =>
          if ctx.hasCtxLocals then
            throwCheckAssignmentFailure -- It is not a pattern, then we fail and fall back to FO unification
          else if mvarDecl.lctx.isSubPrefixOf ctx.mvarDecl.lctx ctx.fvars then
            /- The local context of `mvar` - free variables being abstracted is a subprefix of the metavariable being assigned.
               We "subtract" variables being abstracted because we use `elimMVarDeps` -/
            pure mvar
          else if mvarDecl.depth != (← getMCtx).depth || mvarDecl.kind.isSyntheticOpaque then
            traceM `Meta.isDefEq.assign.readOnlyMVarWithBiggerLCtx <| addAssignmentInfo (mkMVar mvarId)
            throwCheckAssignmentFailure
          else
            let ctxMeta ← readThe Meta.Context
            if ctxMeta.config.ctxApprox && ctx.mvarDecl.lctx.isSubPrefixOf mvarDecl.lctx then
              /- Create an auxiliary metavariable with a smaller context and "checked" type.
                 Note that `mvarType` may be different from `mvarDecl.type`. Example: `mvarType` contains
                 a metavariable that we also need to reduce the context.

                 We remove from `ctx.mvarDecl.lctx` any variable that is not in `mvarDecl.lctx`
                 or in `ctx.fvars`. We don't need to remove the ones in `ctx.fvars` because
                 `elimMVarDeps` will take care of them.

                 First, we collect `toErase` the variables that need to be erased.
                 Notat that if a variable is `ctx.fvars`, but it depends on variable at `toErase`,
                 we must also erase it.
              -/
              let toErase ← mvarDecl.lctx.foldlM (init := #[]) fun toErase localDecl => do
                if ctx.mvarDecl.lctx.contains localDecl.fvarId then
                  return toErase
                else if ctx.fvars.any fun fvar => fvar.fvarId! == localDecl.fvarId then
                  if (← findLocalDeclDependsOn localDecl fun fvarId => toErase.contains fvarId) then
                    -- localDecl depends on a variable that will be erased. So, we must add it to `toErase` too
                    return toErase.push localDecl.fvarId
                  else
                    return toErase
                else
                  return toErase.push localDecl.fvarId
              let lctx := toErase.foldl (init := mvarDecl.lctx) fun lctx toEraseFVar =>
                lctx.erase toEraseFVar
              /- Compute new set of local instances. -/
              let localInsts := mvarDecl.localInstances.filter fun localInst => !toErase.contains localInst.fvar.fvarId!
              let mvarType ← check mvarDecl.type
              let newMVar ← mkAuxMVar lctx localInsts mvarType mvarDecl.numScopeArgs
              mvarId.assign newMVar
              pure newMVar
            else
              traceM `Meta.isDefEq.assign.readOnlyMVarWithBiggerLCtx <| addAssignmentInfo (mkMVar mvarId)
              throwCheckAssignmentFailure

  /--
    Auxiliary function used to "fix" subterms of the form `?m x_1 ... x_n` where `x_i`s are free variables,
    and one of them is out-of-scope.
    See `Expr.app` case at `check`.
    If `ctxApprox` is true, then we solve this case by creating a fresh metavariable ?n with the correct scope,
    an assigning `?m := fun _ ... _ => ?n` -/
  partial def assignToConstFun (mvar : Expr) (numArgs : Nat) (newMVar : Expr) : MetaM Bool := do
    let mvarType ← inferType mvar
    forallBoundedTelescope mvarType numArgs fun xs _ => do
      if xs.size != numArgs then pure false
      else
        let some v ← mkLambdaFVarsWithLetDeps xs newMVar | return false
        match (← checkAssignmentAux mvar.mvarId! #[] false v) with
        | some v => checkTypesAndAssign mvar v
        | none   => return false

  -- See checkAssignment
  partial def checkAssignmentAux (mvarId : MVarId) (fvars : Array Expr) (hasCtxLocals : Bool) (v : Expr) : MetaM (Option Expr) := do
    run (check v) mvarId fvars hasCtxLocals v

  partial def checkApp (e : Expr) : CheckAssignmentM Expr :=
    e.withApp fun f args => do
      let ctxMeta ← readThe Meta.Context
      if f.isMVar && ctxMeta.config.ctxApprox && args.all Expr.isFVar then
        let f ← check f
        catchInternalId outOfScopeExceptionId
          (do
            let args ← args.mapM check
            return mkAppN f args)
          (fun ex => do
            if !f.isMVar then
              throw ex
            else if (← f.mvarId!.isDelayedAssigned) then
              throw ex
            else
              let eType ← inferType e
              let mvarType ← check eType
              /- Create an auxiliary metavariable with a smaller context and "checked" type, assign `?f := fun _ => ?newMVar`
                    Note that `mvarType` may be different from `eType`. -/
              let ctx ← read
              let newMVar ← mkAuxMVar ctx.mvarDecl.lctx ctx.mvarDecl.localInstances mvarType
              if (← assignToConstFun f args.size newMVar) then
                pure newMVar
              else
                throw ex)
      else
        let f ← check f
        let args ← args.mapM check
        return mkAppN f args

  partial def check (e : Expr) : CheckAssignmentM Expr := do
    if !e.hasExprMVar && !e.hasFVar then
      return e
    else checkCache e fun _ =>
      match e with
      | Expr.mdata _ b       => return e.updateMData! (← check b)
      | Expr.proj _ _ s      => return e.updateProj! (← check s)
      | Expr.lam _ d b _     => return e.updateLambdaE! (← check d) (← check b)
      | Expr.forallE _ d b _ => return e.updateForallE! (← check d) (← check b)
      | Expr.letE _ t v b _  => return e.updateLet! (← check t) (← check v) (← check b)
      | Expr.bvar ..         => return e
      | Expr.sort ..         => return e
      | Expr.const ..        => return e
      | Expr.lit ..          => return e
      | Expr.fvar ..         => checkFVar e
      | Expr.mvar ..         => checkMVar e
      | Expr.app ..          =>
        try
          checkApp e
        catch ex => match ex with
          | .internal id =>
            /-
            If `ex` is an `CheckAssignmentM` internal exception and `e` is a beta-redex, we reduce `e` and try again.
            This is useful for assignments such as `?m := (fun _ => A) a` where `a` is free variable that is not in
            the scope of `?m`.
            Note that, we do not try expensive reductions (e.g., `delta`). Thus, the following assignment
            ```lean
            ?m := Function.const 0 a
            ```
            still fails because we do reduce the rhs to `0`. We assume this is not an issue in practice.
            -/
            if (id == outOfScopeExceptionId || id == checkAssignmentExceptionId) && e.isHeadBetaTarget then
              checkApp e.headBeta
            else
              throw ex
          | _ => throw ex

        -- TODO: investigate whether the following feature is too expensive or not
        /-
        catchInternalIds [checkAssignmentExceptionId, outOfScopeExceptionId]
          (checkApp e)
          fun ex => do
            let e' ← whnfR e
            if e != e' then
              check e'
            else
              throw ex
        -/
end

end CheckAssignment

namespace CheckAssignmentQuick

partial def check
    (hasCtxLocals : Bool)
    (mctx : MetavarContext) (lctx : LocalContext) (mvarDecl : MetavarDecl) (mvarId : MVarId) (fvars : Array Expr) (e : Expr) : Bool :=
  let rec visit (e : Expr) : Bool :=
    if !e.hasExprMVar && !e.hasFVar then
      true
    else match e with
    | Expr.mdata _ b       => visit b
    | Expr.proj _ _ s      => visit s
    | Expr.app f a         => visit f && visit a
    | Expr.lam _ d b _     => visit d && visit b
    | Expr.forallE _ d b _ => visit d && visit b
    | Expr.letE _ t v b _  => visit t && visit v && visit b
    | Expr.bvar ..         => true
    | Expr.sort ..         => true
    | Expr.const ..        => true
    | Expr.lit ..          => true
    | Expr.fvar fvarId ..  =>
      if mvarDecl.lctx.contains fvarId then true
      else match lctx.find? fvarId with
        | some (LocalDecl.ldecl ..) => false -- need expensive CheckAssignment.check
        | _ =>
          if fvars.any fun x => x.fvarId! == fvarId then true
          else false -- We could throw an exception here, but we would have to use ExceptM. So, we let CheckAssignment.check do it
    | Expr.mvar mvarId'    =>
      match mctx.getExprAssignmentCore? mvarId' with
      | some _ => false -- use CheckAssignment.check to instantiate
      | none   =>
        if mvarId' == mvarId then false -- occurs check failed, use CheckAssignment.check to throw exception
        else match mctx.findDecl? mvarId' with
          | none           => false
          | some mvarDecl' =>
            if hasCtxLocals then false -- use CheckAssignment.check
            else if mvarDecl'.lctx.isSubPrefixOf mvarDecl.lctx fvars then true
            else false -- use CheckAssignment.check
  visit e

end CheckAssignmentQuick

/--
  Auxiliary function for handling constraints of the form `?m a₁ ... aₙ =?= v`.
  It will check whether we can perform the assignment
  ```
  ?m := fun fvars => v
  ```
  The result is `none` if the assignment can't be performed.
  The result is `some newV` where `newV` is a possibly updated `v`. This method may need
  to unfold let-declarations. -/
def checkAssignment (mvarId : MVarId) (fvars : Array Expr) (v : Expr) : MetaM (Option Expr) := do
  /- Check whether `mvarId` occurs in the type of `fvars` or not. If it does, return `none`
     to prevent us from creating the cyclic assignment `?m := fun fvars => v` -/
  for fvar in fvars do
    unless (← occursCheck mvarId (← inferType fvar)) do
      return none
  if !v.hasExprMVar && !v.hasFVar then
    pure (some v)
  else
    let mvarDecl ← mvarId.getDecl
    let hasCtxLocals := fvars.any fun fvar => mvarDecl.lctx.containsFVar fvar
    let ctx ← read
    let mctx ← getMCtx
    if CheckAssignmentQuick.check hasCtxLocals mctx ctx.lctx mvarDecl mvarId fvars v then
      pure (some v)
    else
      let v ← instantiateMVars v
      CheckAssignment.checkAssignmentAux mvarId fvars hasCtxLocals v

private def processAssignmentFOApproxAux (mvar : Expr) (args : Array Expr) (v : Expr) : MetaM Bool :=
  match v with
  | .mdata _ e   => processAssignmentFOApproxAux mvar args e
  | Expr.app f a =>
    if args.isEmpty then
      pure false
    else
      Meta.isExprDefEqAux args.back a <&&> Meta.isExprDefEqAux (mkAppRange mvar 0 (args.size - 1) args) f
  | _            => pure false

/--
  Auxiliary method for applying first-order unification. It is an approximation.
  Remark: this method is trying to solve the unification constraint:

      ?m a₁ ... aₙ =?= v

   It is uses processAssignmentFOApproxAux, if it fails, it tries to unfold `v`.

   We have added support for unfolding here because we want to be able to solve unification problems such as

      ?m Unit =?= ITactic

   where `ITactic` is defined as

   def ITactic := Tactic Unit
-/
private partial def processAssignmentFOApprox (mvar : Expr) (args : Array Expr) (v : Expr) : MetaM Bool :=
  let rec loop (v : Expr) := do
    let cfg ← getConfig
    if !cfg.foApprox then
      pure false
    else
      trace[Meta.isDefEq.foApprox] "{mvar} {args} := {v}"
      let v := v.headBeta
      if (← checkpointDefEq <| processAssignmentFOApproxAux mvar args v) then
        pure true
      else
        match (← unfoldDefinition? v) with
        | none   => pure false
        | some v => loop v
  loop v

private partial def simpAssignmentArgAux (e : Expr) : MetaM Expr := do
  match e with
  | .mdata _ e   => simpAssignmentArgAux e
  | .fvar fvarId =>
    let some value ← fvarId.getValue? | return e
    simpAssignmentArgAux value
  | _ => return e

/-- Auxiliary procedure for processing `?m a₁ ... aₙ =?= v`.
   We apply it to each `aᵢ`. It instantiates assigned metavariables if `aᵢ` is of the form `f[?n] b₁ ... bₘ`,
   and then removes metadata, and zeta-expand let-decls. -/
private def simpAssignmentArg (arg : Expr) : MetaM Expr := do
  let arg ← if arg.getAppFn.hasExprMVar then instantiateMVars arg else pure arg
  simpAssignmentArgAux arg

/-- Assign `mvar := fun a_1 ... a_{numArgs} => v`.
   We use it at `processConstApprox` and `isDefEqMVarSelf` -/
private def assignConst (mvar : Expr) (numArgs : Nat) (v : Expr) : MetaM Bool := do
  let mvarDecl ← mvar.mvarId!.getDecl
  forallBoundedTelescope mvarDecl.type numArgs fun xs _ => do
    if xs.size != numArgs then
      pure false
    else
      let some v ← mkLambdaFVarsWithLetDeps xs v | pure false
      match (← checkAssignment mvar.mvarId! #[] v) with
      | none   => pure false
      | some v =>
        trace[Meta.isDefEq.constApprox] "{mvar} := {v}"
        checkTypesAndAssign mvar v

/--
  Auxiliary procedure for solving `?m args =?= v` when `args[:patternVarPrefix]` contains
  only pairwise distinct free variables.
  Let `args[:patternVarPrefix] = #[a₁, ..., aₙ]`, and `args[patternVarPrefix:] = #[b₁, ..., bᵢ]`,
  this procedure first reduces the constraint to
  ```
  ?m a₁ ... aₙ =?= fun x₁ ... xᵢ => v
  ```
  where the left-hand-side is a constant function.
  Then, it tries to find the longest prefix `#[a₁, ..., aⱼ]` of `#[a₁, ..., aₙ]` such that the following assignment is valid.
  ```
  ?m := fun y₁ ... y‌ⱼ => (fun y_{j+1} ... yₙ x₁ ... xᵢ => v)[a₁/y₁, .., aⱼ/yⱼ]
  ```
  That is, after the longest prefix is found, we solve the constraint as the lhs was a pattern. See the definition of "pattern" above.
-/
private partial def processConstApprox (mvar : Expr) (args : Array Expr) (patternVarPrefix : Nat) (v : Expr) : MetaM Bool := do
  trace[Meta.isDefEq.constApprox] "{mvar} {args} := {v}"
  let rec defaultCase : MetaM Bool := assignConst mvar args.size v
  let cfg ← getConfig
  let mvarId := mvar.mvarId!
  let mvarDecl ← mvarId.getDecl
  let numArgs := args.size
  if mvarDecl.numScopeArgs != numArgs && !cfg.constApprox then
    return false
  else if patternVarPrefix == 0 then
    defaultCase
  else
    let argsPrefix : Array Expr := args[:patternVarPrefix]
    let type ← instantiateForall mvarDecl.type argsPrefix
    let suffixSize := numArgs - argsPrefix.size
    forallBoundedTelescope type suffixSize fun xs _ => do
      if xs.size != suffixSize then
        defaultCase
      else
        let some v ← mkLambdaFVarsWithLetDeps xs v | defaultCase
        let rec go (argsPrefix : Array Expr) (v : Expr) : MetaM Bool := do
          trace[Meta.isDefEq] "processConstApprox.go {mvar} {argsPrefix} := {v}"
          let rec cont : MetaM Bool := do
            if argsPrefix.isEmpty then
              defaultCase
            else
              let some v ← mkLambdaFVarsWithLetDeps #[argsPrefix.back] v | defaultCase
              go argsPrefix.pop v
          match (← checkAssignment mvarId argsPrefix v) with
          | none      => cont
          | some vNew =>
            let some vNew ← mkLambdaFVarsWithLetDeps argsPrefix vNew | cont
            if argsPrefix.any (fun arg => mvarDecl.lctx.containsFVar arg) then
              /- We need to type check `vNew` because abstraction using `mkLambdaFVars` may have produced
                 a type incorrect term. See discussion at A2 -/
              (isTypeCorrect vNew <&&> checkTypesAndAssign mvar vNew) <||> cont
            else
              checkTypesAndAssign mvar vNew <||> cont
        go argsPrefix v

/-- Tries to solve `?m a₁ ... aₙ =?= v` by assigning `?m`.
    It assumes `?m` is unassigned. -/
private partial def processAssignment (mvarApp : Expr) (v : Expr) : MetaM Bool :=
  withTraceNodeBefore `Meta.isDefEq.assign (return m!"{mvarApp} := {v}") do
    let mvar := mvarApp.getAppFn
    let mvarDecl ← mvar.mvarId!.getDecl
    let rec process (i : Nat) (args : Array Expr) (v : Expr) := do
      let cfg ← getConfig
      let useFOApprox (args : Array Expr) : MetaM Bool :=
        processAssignmentFOApprox mvar args v <||> processConstApprox mvar args i v
      if h : i < args.size then
        let arg := args.get ⟨i, h⟩
        let arg ← simpAssignmentArg arg
        let args := args.set ⟨i, h⟩ arg
        match arg with
        | Expr.fvar fvarId =>
          if args[0:i].any fun prevArg => prevArg == arg then
            useFOApprox args
          else if mvarDecl.lctx.contains fvarId && !cfg.quasiPatternApprox then
            useFOApprox args
          else
            process (i+1) args v
        | _ =>
          useFOApprox args
      else
        let v ← instantiateMVars v -- enforce A4
        if v.getAppFn == mvar then
          -- using A6
          useFOApprox args
        else
          let mvarId := mvar.mvarId!
          match (← checkAssignment mvarId args v) with
          | none   => useFOApprox args
          | some v => do
            trace[Meta.isDefEq.assign.beforeMkLambda] "{mvar} {args} := {v}"
            let some v ← mkLambdaFVarsWithLetDeps args v | return false
            if args.any (fun arg => mvarDecl.lctx.containsFVar arg) then
              /- We need to type check `v` because abstraction using `mkLambdaFVars` may have produced
                 a type incorrect term. See discussion at A2 -/
              if (← isTypeCorrect v) then
                checkTypesAndAssign mvar v
              else
                trace[Meta.isDefEq.assign.typeError] "{mvar} := {v}"
                useFOApprox args
            else
              checkTypesAndAssign mvar v
    process 0 mvarApp.getAppArgs v

/--
  Similar to processAssignment, but if it fails, compute v's whnf and try again.
  This helps to solve constraints such as `?m =?= { α := ?m, ... }.α`
  Note this is not perfect solution since we still fail occurs check for constraints such as
  ```lean
    ?m =?= List { α := ?m, β := Nat }.β
  ```
-/
private def processAssignment' (mvarApp : Expr) (v : Expr) : MetaM Bool := do
  if (← processAssignment mvarApp v) then
    return true
  else
    let vNew ← whnf v
    if vNew != v then
      if mvarApp == vNew then
        return true
      else
        processAssignment mvarApp vNew
    else
      return false

private def isDeltaCandidate? (t : Expr) : MetaM (Option ConstantInfo) := do
  match t.getAppFn with
  | Expr.const c _ =>
    match (← getUnfoldableConst? c) with
    | r@(some info) => if info.hasValue then return r else return none
    | _             => return none
  | _ => pure none

/-- Auxiliary method for isDefEqDelta -/
private def isListLevelDefEq (us vs : List Level) : MetaM LBool :=
  toLBoolM <| isListLevelDefEqAux us vs

/-- Auxiliary method for isDefEqDelta -/
private def isDefEqLeft (fn : Name) (t s : Expr) : MetaM LBool := do
  trace[Meta.isDefEq.delta.unfoldLeft] fn
  toLBoolM <| Meta.isExprDefEqAux t s

/-- Auxiliary method for isDefEqDelta -/
private def isDefEqRight (fn : Name) (t s : Expr) : MetaM LBool := do
  trace[Meta.isDefEq.delta.unfoldRight] fn
  toLBoolM <| Meta.isExprDefEqAux t s

/-- Auxiliary method for isDefEqDelta -/
private def isDefEqLeftRight (fn : Name) (t s : Expr) : MetaM LBool := do
  trace[Meta.isDefEq.delta.unfoldLeftRight] fn
  toLBoolM <| Meta.isExprDefEqAux t s

/-- Try to solve `f a₁ ... aₙ =?= f b₁ ... bₙ` by solving `a₁ =?= b₁, ..., aₙ =?= bₙ`.

    Auxiliary method for isDefEqDelta -/
private def tryHeuristic (t s : Expr) : MetaM Bool := do
  let mut t := t
  let mut s := s
  let tFn := t.getAppFn
  let sFn := s.getAppFn
  let info ← getConstInfo tFn.constName!
  /- We only use the heuristic when `f` is a regular definition or an auxiliary `match` application.
     That is, it is not marked an abbreviation (e.g., a user-facing projection) or as opaque (e.g., proof).
     We check whether terms contain metavariables to make sure we can solve constraints such
     as `S.proj ?x =?= S.proj t` without performing delta-reduction.
     That is, we are assuming the heuristic implemented by this method is seldom effective
     when `t` and `s` do not have metavariables, are not structurally equal, and `f` is an abbreviation.
     On the other hand, by unfolding `f`, we often produce smaller terms.

     Recall that auxiliary `match` definitions are marked as abbreviations, but we must use the heuristic on
     them since they will not be unfolded when smartUnfolding is turned on. The abbreviation annotation in this
     case is used to help the kernel type checker. -/
  unless info.hints.isRegular || isMatcherCore (← getEnv) tFn.constName! do
    unless t.hasExprMVar || s.hasExprMVar do
      return false
  withTraceNodeBefore `Meta.isDefEq.delta (return m!"{t} =?= {s}") do
    /-
      We process arguments before universe levels to reduce a source of brittleness in the TC procedure.

      In the TC procedure, we can solve problems containing metavariables.
      If the TC procedure tries to assign one of these metavariables, it interrupts the search
      using a "stuck" exception. The elaborator catches it, and "interprets" it as "we should try again later".
      Now suppose we have a TC problem, and there are two "local" candidate instances we can try: "bad" and "good".
      The "bad" candidate is stuck because of a universe metavariable in the TC problem.
      If we try "bad" first, the TC procedure is interrupted. Moreover, if we have ignored the exception,
      "bad" would fail anyway trying to assign two different free variables `α =?= β`.
      Example: `Preorder.{?u} α =?= Preorder.{?v} β`, where `?u` and `?v` are universe metavariables that were
      not created by the TC procedure.
      The key issue here is that we have an `isDefEq t s` invocation that is interrupted by the "stuck" exception,
      but it would have failed anyway if we had continued processing it.
      By solving the arguments first, we make the example above fail without throwing the "stuck" exception.

      TODO: instead of throwing an exception as soon as we get stuck, we should just set a flag.
      Then the entry-point for `isDefEq` checks the flag before returning `true`.
    -/
    checkpointDefEq do
      isDefEqArgs tFn t.getAppArgs s.getAppArgs <&&>
        isListLevelDefEqAux tFn.constLevels! sFn.constLevels!

/-- Auxiliary method for isDefEqDelta -/
private abbrev unfold (e : Expr) (failK : MetaM α) (successK : Expr → MetaM α) : MetaM α := do
  match (← unfoldDefinition? e) with
  | some e => successK e
  | none   => failK

/-- Auxiliary method for isDefEqDelta -/
private def unfoldBothDefEq (fn : Name) (t s : Expr) : MetaM LBool := do
  match t, s with
  | Expr.const _ ls₁, Expr.const _ ls₂ => isListLevelDefEq ls₁ ls₂
  | Expr.app _ _,     Expr.app _ _     =>
    if (← tryHeuristic t s) then
      pure LBool.true
    else
      unfold t
       (unfold s (pure LBool.undef) (fun s => isDefEqRight fn t s))
       (fun t => unfold s (isDefEqLeft fn t s) (fun s => isDefEqLeftRight fn t s))
  | _, _ => pure LBool.false

private def sameHeadSymbol (t s : Expr) : Bool :=
  match t.getAppFn, s.getAppFn with
  | Expr.const c₁ _, Expr.const c₂ _ => c₁ == c₂
  | _,               _               => false

/--
  - If headSymbol (unfold t) == headSymbol s, then unfold t
  - If headSymbol (unfold s) == headSymbol t, then unfold s
  - Otherwise unfold t and s if possible.

  Auxiliary method for isDefEqDelta -/
private def unfoldComparingHeadsDefEq (tInfo sInfo : ConstantInfo) (t s : Expr) : MetaM LBool :=
  unfold t
    (unfold s
      (pure LBool.undef) -- `t` and `s` failed to be unfolded
      (fun s => isDefEqRight sInfo.name t s))
    (fun tNew =>
      if sameHeadSymbol tNew s then
        isDefEqLeft tInfo.name tNew s
      else
        unfold s
          (isDefEqLeft tInfo.name tNew s)
          (fun sNew =>
            if sameHeadSymbol t sNew then
              isDefEqRight sInfo.name t sNew
            else
              isDefEqLeftRight tInfo.name tNew sNew))

/-- If `t` and `s` do not contain metavariables, then use
    kernel definitional equality heuristics.
    Otherwise, use `unfoldComparingHeadsDefEq`.

    Auxiliary method for isDefEqDelta -/
private def unfoldDefEq (tInfo sInfo : ConstantInfo) (t s : Expr) : MetaM LBool :=
  if !t.hasExprMVar && !s.hasExprMVar then
    /- If `t` and `s` do not contain metavariables,
       we simulate strategy used in the kernel. -/
    if tInfo.hints.lt sInfo.hints then
      unfold t (unfoldComparingHeadsDefEq tInfo sInfo t s) fun t => isDefEqLeft tInfo.name t s
    else if sInfo.hints.lt tInfo.hints then
      unfold s (unfoldComparingHeadsDefEq tInfo sInfo t s) fun s => isDefEqRight sInfo.name t s
    else
      unfoldComparingHeadsDefEq tInfo sInfo t s
  else
    unfoldComparingHeadsDefEq tInfo sInfo t s

/--
  When `TransparencyMode` is set to `default` or `all`.
  If `t` is reducible and `s` is not ==> `isDefEqLeft  (unfold t) s`
  If `s` is reducible and `t` is not ==> `isDefEqRight t (unfold s)`

  Otherwise, use `unfoldDefEq`

  Auxiliary method for isDefEqDelta -/
private def unfoldReducibeDefEq (tInfo sInfo : ConstantInfo) (t s : Expr) : MetaM LBool := do
  if (← shouldReduceReducibleOnly) then
    unfoldDefEq tInfo sInfo t s
  else
    let tReducible ← isReducible tInfo.name
    let sReducible ← isReducible sInfo.name
    if tReducible && !sReducible then
      unfold t (unfoldDefEq tInfo sInfo t s) fun t => isDefEqLeft tInfo.name t s
    else if !tReducible && sReducible then
      unfold s (unfoldDefEq tInfo sInfo t s) fun s => isDefEqRight sInfo.name t s
    else
      unfoldDefEq tInfo sInfo t s

/--
  This is an auxiliary method for isDefEqDelta.
  If `t` is a (non-class) projection function application and `s` is not ==> `isDefEqRight t (unfold s)`
  If `s` is a (non-class) projection function application and `t` is not ==> `isDefEqRight (unfold t) s`
  Otherwise, use `unfoldReducibeDefEq`

  One motivation for the heuristic above is unification problems such as
  ```
  id (?m.1) =?= (a, b).1
  ```
  We want to reduce the lhs instead of the rhs, and eventually assign `?m := (a, b)`.

  Another motivation for the heuristic above is unification problems such as
  ```
  List.length (a :: as) =?= HAdd.hAdd (List.length as) 1
  ```

  However, for class projections, we also unpack them and check whether the result function is the one
  on the other side. This is relevant for unification problems such as
  ```
  Foo.pow x 256 =?= Pow.pow x 256
  ```
  where the the `Pow` instance is wrapping `Foo.pow`
  See issue #1419 for the complete example.
-/
private partial def unfoldNonProjFnDefEq (tInfo sInfo : ConstantInfo) (t s : Expr) : MetaM LBool := do
  let tProjInfo? ← getProjectionFnInfo? tInfo.name
  let sProjInfo? ← getProjectionFnInfo? sInfo.name
  if let some tNew ← packedInstanceOf? tProjInfo? t sInfo.name then
    isDefEqLeft tInfo.name tNew s
  else if let some sNew ← packedInstanceOf? sProjInfo? s tInfo.name then
    isDefEqRight sInfo.name t sNew
  else  match tProjInfo?, sProjInfo? with
    | some _, none => unfold s (unfoldDefEq tInfo sInfo t s) fun s => isDefEqRight sInfo.name t s
    | none, some _ => unfold t (unfoldDefEq tInfo sInfo t s) fun t => isDefEqLeft tInfo.name t s
    | _, _ => unfoldReducibeDefEq tInfo sInfo t s
where
  packedInstanceOf? (projInfo? : Option ProjectionFunctionInfo) (e : Expr) (declName : Name) : MetaM (Option Expr) := do
    let some { fromClass := true, .. } := projInfo? | return none -- It is not a class projection
    let some e ← unfoldDefinition? e | return none
    let e ← whnfCore e
    if e.isAppOf declName then return some e
    let .const name _ := e.getAppFn | return none
    -- Keep going if new `e` is also a class projection
    packedInstanceOf? (← getProjectionFnInfo? name) e declName

/--
  isDefEq by lazy delta reduction.
  This method implements many different heuristics:
  1- If only `t` can be unfolded => then unfold `t` and continue
  2- If only `s` can be unfolded => then unfold `s` and continue
  3- If `t` and `s` can be unfolded and they have the same head symbol, then
     a) First try to solve unification by unifying arguments.
     b) If it fails, unfold both and continue.
     Implemented by `unfoldBothDefEq`
  4- If `t` is a projection function application and `s` is not => then unfold `s` and continue.
  5- If `s` is a projection function application and `t` is not => then unfold `t` and continue.
  Remark: 4&5 are implemented by `unfoldNonProjFnDefEq`
  6- If `t` is reducible and `s` is not => then unfold `t` and continue.
  7- If `s` is reducible and `t` is not => then unfold `s` and continue
  Remark: 6&7 are implemented by `unfoldReducibeDefEq`
  8- If `t` and `s` do not contain metavariables, then use heuristic used in the Kernel.
     Implemented by `unfoldDefEq`
  9- If `headSymbol (unfold t) == headSymbol s`, then unfold t and continue.
  10- If `headSymbol (unfold s) == headSymbol t`, then unfold s
  11- Otherwise, unfold `t` and `s` and continue.
  Remark: 9&10&11 are implemented by `unfoldComparingHeadsDefEq` -/
private def isDefEqDelta (t s : Expr) : MetaM LBool := do
  let tInfo? ← isDeltaCandidate? t
  let sInfo? ← isDeltaCandidate? s
  match tInfo?, sInfo? with
  | none,       none       => pure LBool.undef
  | some tInfo, none       => unfold t (pure LBool.undef) fun t => isDefEqLeft tInfo.name t s
  | none,       some sInfo => unfold s (pure LBool.undef) fun s => isDefEqRight sInfo.name t s
  | some tInfo, some sInfo =>
    if tInfo.name == sInfo.name then
      unfoldBothDefEq tInfo.name t s
    else
      unfoldNonProjFnDefEq tInfo sInfo t s

private def isAssigned : Expr → MetaM Bool
  | Expr.mvar mvarId => mvarId.isAssigned
  | _                => pure false

private def expandDelayedAssigned? (t : Expr) : MetaM (Option Expr) := do
  let tFn := t.getAppFn
  if !tFn.isMVar then return none
  let some { fvars, mvarIdPending } ← getDelayedMVarAssignment? tFn.mvarId! | return none
  let tNew ← instantiateMVars t
  if tNew != t then return some tNew
  /-
    If `assignSyntheticOpaque` is true, we must follow the delayed assignment.
    Recall a delayed assignment `mvarId [xs] := mvarIdPending` is morally an assignment
    `mvarId := fun xs => mvarIdPending` where `xs` are free variables in the scope of `mvarIdPending`,
    but not in the scope of `mvarId`. We can only perform the abstraction when `mvarIdPending` has been fully synthesized.
    That is, `instantiateMVars (mkMVar mvarIdPending)` does not contain any expression metavariables.
    Here we just consume `fvar.size` arguments. That is, if `t` is of the form `mvarId as bs` where `as.size == fvars.size`,
    we return `mvarIdPending bs`.

    TODO: improve this transformation. Here is a possible improvement.
    Assume `t` is of the form `?m as` where `as` represent the arguments, and we are trying to solve
    `?m as =?= s[as]` where `s[as]` represents a term containing occurrences of `as`.
    We could try to compute the solution as usual `?m := fun ys => s[as/ys]`
    We also have the delayed assignment `?m [xs] := ?n`, where `xs` are variables in the scope of `?n`,
    and this delayed assignment is morally `?m := fun xs => ?n`.
    Thus, we can reduce `?m as =?= s[as]` to `?n =?= s[as/xs]`, and solve it using `?n`'s local context.
    This is more precise than simply dropping the arguments `as`.
  -/
  unless (← getConfig).assignSyntheticOpaque do return none
  let tArgs := t.getAppArgs
  if tArgs.size < fvars.size then return none
  return some (mkAppRange (mkMVar mvarIdPending) fvars.size tArgs.size tArgs)

private def isAssignable : Expr → MetaM Bool
  | Expr.mvar mvarId => do let b ← mvarId.isReadOnlyOrSyntheticOpaque; pure (!b)
  | _                => pure false

private def etaEq (t s : Expr) : Bool :=
  match t.etaExpanded? with
  | some t => t == s
  | none   => false

/--
  Helper method for implementing `isDefEqProofIrrel`. Execute `k` with a transparency setting
  that is at least as strong as `.default`. This is important for modules that use the `.reducible`
  setting (e.g., `simp`, `rw`, etc). We added this feature to address issue #1302.
  ```lean
  @[simp] theorem get_cons_zero {as : List α} : (a :: as).get ⟨0, Nat.zero_lt_succ _⟩ = a := rfl

  example (a b c : α) : [a, b, c].get ⟨0, by simp⟩ = a := by simp
  ```
  In the example above `simp` fails to use `get_cons_zero` because it fails to establish that
  the proof objects are definitionally equal using proof irrelevance. In this example,
  the propositions are
  ```lean
  0 < Nat.succ (List.length [b, c]) =?= 0 < Nat.succ (Nat.succ (Nat.succ 0))
  ```
  So, unless we can unfold `List.length`, it fails.

  Remark: if this becomes a performance bottleneck, we should add a flag to control when it is used.
  Then, we can enable the flag only when applying `simp` and `rw` theorems.
-/
private def withProofIrrelTransparency (k : MetaM α) : MetaM α :=
  withAtLeastTransparency .default k

private def isDefEqProofIrrel (t s : Expr) : MetaM LBool := do
  if (← getConfig).proofIrrelevance then
    match (← isProofQuick t) with
    | LBool.false =>
      pure LBool.undef
    | LBool.true  =>
      let tType ← inferType t
      let sType ← inferType s
      toLBoolM <| withProofIrrelTransparency <| Meta.isExprDefEqAux tType sType
    | LBool.undef =>
      let tType ← inferType t
      if (← isProp tType) then
        let sType ← inferType s
        toLBoolM <| withProofIrrelTransparency <| Meta.isExprDefEqAux tType sType
      else
        pure LBool.undef
  else
    pure LBool.undef

/-- Try to solve constraint of the form `?m args₁ =?= ?m args₂`.
   - First try to unify `args₁` and `args₂`, and return true if successful
   - Otherwise, try to assign `?m` to a constant function of the form `fun x_1 ... x_n => ?n`
     where `?n` is a fresh metavariable. See `assignConst`. -/
private def isDefEqMVarSelf (mvar : Expr) (args₁ args₂ : Array Expr) : MetaM Bool := do
  if args₁.size != args₂.size then
    pure false
  else if (← isDefEqArgs mvar args₁ args₂) then
    pure true
  else if !(← isAssignable mvar) then
    pure false
  else
    let cfg ← getConfig
    let mvarId := mvar.mvarId!
    let mvarDecl ← mvarId.getDecl
    if mvarDecl.numScopeArgs == args₁.size || cfg.constApprox then
      let type ← inferType (mkAppN mvar args₁)
      let auxMVar ← mkAuxMVar mvarDecl.lctx mvarDecl.localInstances type
      assignConst mvar args₁.size auxMVar
    else
      pure false

/-- Remove unnecessary let-decls -/
private def consumeLet : Expr → Expr
  | e@(Expr.letE _ _ _ b _) => if b.hasLooseBVars then e else consumeLet b
  | e                       => e

mutual

private partial def isDefEqQuick (t s : Expr) : MetaM LBool :=
  let t := consumeLet t
  let s := consumeLet s
  match t, s with
  | .lit  l₁,      .lit l₂     => return (l₁ == l₂).toLBool
  | .sort u,       .sort v     => toLBoolM <| isLevelDefEqAux u v
  | .lam ..,       .lam ..     => if t == s then pure LBool.true else toLBoolM <| isDefEqBinding t s
  | .forallE ..,   .forallE .. => if t == s then pure LBool.true else toLBoolM <| isDefEqBinding t s
  -- | Expr.mdata _ t _,    s                   => isDefEqQuick t s
  -- | t,                   Expr.mdata _ s _    => isDefEqQuick t s
  | .fvar fvarId₁, .fvar fvarId₂ => do
    if (← fvarId₁.isLetVar <||> fvarId₂.isLetVar) then
      return LBool.undef
    else if fvarId₁ == fvarId₂ then
      return LBool.true
    else
      isDefEqProofIrrel t s
  | t, s =>
    isDefEqQuickOther t s

private partial def isDefEqQuickOther (t s : Expr) : MetaM LBool := do
  /-
    We used to eagerly consume all metadata (see commented lines at `isDefEqQuick`),
    but it was unnecessarily removing helpful annotations
    for the pretty-printer. For example, consider the following example.
    ```
    constant p : Nat → Prop
    constant q : Nat → Prop

    theorem p_of_q : q x → p x := sorry

    theorem pletfun : p (let_fun x := 0; x + 1) := by
      -- ⊢ p (let_fun x := 0; x + 1)
      apply p_of_q -- If we eagerly consume all metadata, the let_fun annotation is lost during `isDefEq`
      -- ⊢ q ((fun x => x + 1) 0)
      sorry
    ```
    However, pattern annotations (`inaccessible?` and `patternWithRef?`) must be consumed.
    The frontend relies on the fact that is must not be propagated by `isDefEq`.
    Thus, we consume it here. This is a bit hackish since it is very adhoc.
    We might have other annotations in the future that we should not preserve.
    Perhaps, we should mark the annotations we do want to preserve
    (e.g., hints for the pretty printer), and consume all others.
  -/
  if let some t := patternAnnotation? t then
    isDefEqQuick t s
  else if let some s := patternAnnotation? s then
    isDefEqQuick t s
  else if t == s then
    return LBool.true
  else if etaEq t s || etaEq s t then
    return LBool.true  -- t =?= (fun xs => t xs)
  else
    let tFn := t.getAppFn
    let sFn := s.getAppFn
    if !tFn.isMVar && !sFn.isMVar then
      return LBool.undef
    else if (← isAssigned tFn) then
      let t ← instantiateMVars t
      isDefEqQuick t s
    else if (← isAssigned sFn) then
      let s ← instantiateMVars s
      isDefEqQuick t s
    else if let some t ← expandDelayedAssigned? t then
      isDefEqQuick t s
    else if let some s ← expandDelayedAssigned? s then
      isDefEqQuick t s
    /- Remark: we do not eagerly synthesize synthetic metavariables when the constraint is not stuck.
       Reason: we may fail to solve a constraint of the form `?x =?= A` when the synthesized instance
       is not definitionally equal to `A`. We left the code here as a reminder of this issue. -/
--    else if (← isSynthetic tFn <&&> trySynthPending tFn) then
--      let t ← instantiateMVars t
--     isDefEqQuick t s
--    else if (← isSynthetic sFn <&&> trySynthPending sFn) then
--      let s ← instantiateMVars s
--      isDefEqQuick t s
    else if tFn.isMVar && sFn.isMVar && tFn == sFn then
      Bool.toLBool <$> isDefEqMVarSelf tFn t.getAppArgs s.getAppArgs
    else
      let tAssign? ← isAssignable tFn
      let sAssign? ← isAssignable sFn
      let assignableMsg (b : Bool) := if b then "[assignable]" else "[nonassignable]"
      trace[Meta.isDefEq] "{t} {assignableMsg tAssign?} =?= {s} {assignableMsg sAssign?}"
      if tAssign? && !sAssign? then
        toLBoolM <| processAssignment' t s
      else if !tAssign? && sAssign? then
        toLBoolM <| processAssignment' s t
      else if !tAssign? && !sAssign? then
        /- Trying to unify `?m ... =?= ?n ...` where both `?m` and `?n` cannot be assigned.
           This can happen when both of them are `syntheticOpaque` (e.g., metavars associated with tactics), or a metavariables
           from previous levels.

           If their types are propositions and are defeq, we can solve the constraint by proof irrelevance.
           This test is important for fixing a performance problem exposed by test `isDefEqPerfIssue.lean`.
           Without the proof irrelevance check, this example timeouts. Recall that:

           1- The elaborator has a pending list of things to do: Tactics, TC, etc.
           2- The elaborator only tries tactics after it tried to solve pending TC problems, delayed elaboratio, etc.
              The motivation: avoid unassigned metavariables in goals.
           3- Each pending tactic goal is represented as a metavariable. It is marked as `syntheticOpaque` to make it clear
              that it should not be assigned by unification.
           4- When we abstract a term containing metavariables, we often create new metavariables.
              Example: when abstracting `x` at `f ?m`, we obtain `fun x => f (?m' x)`. If `x` is in the scope of `?m`.
              If `?m` is `syntheticOpaque`, so is `?m'`, and we also have the delayed assignment `?m' x := ?m`
           5- When checking a metavariable assignment, `?m := v` we check whether the type of `?m` is defeq to type of `v`
              with default reducibility setting.

           Now consider the following fragment
           ```
             let a' := g 100 a ⟨i, h⟩ ⟨i - Nat.zero.succ, by exact Nat.lt_of_le_of_lt (Nat.pred_le i) h⟩
             have : a'.size - i >= 0 := sorry
             f (i+1) a'
           ```
           The elaborator tries to synthesize the instance `OfNat Nat 1` before we generate the tactic proof for `by exact ...` (remark 2).
           The solution `instOfNatNat 1` is synthesized. Let `m? a i h a' this` be the "hole" associated with the pending instance.
           Then, `isDefEq` tries to assign `m? a i h a' this := instOfNatNat 1` which is reduced to
           `m? := mkLambdaFVars #[a, i, h, a', this] (instOfNatNat 1)`. Note that, this is an abstraction step (remark 4), and the type
           contains the `syntheticOpaque` metavariable for the pending tactic proof (remark 3). Thus, a new `syntheticOpaque`
           opaque is created (remark 4). Then, `isDefEq` must check whether the type of `?m` is defeq to
           `mkLambdaFVars #[a, i, h, a', this] (instOfNatNat 1)` (remark 5). The two types are almost identical, but they
           contain different `syntheticOpaque` in the subterm corresponding to the `by exact ...` tactic proof. Without the following
           proof irrelevance test, the check will fail, and `isDefEq` timeouts unfolding `g` and its dependencies.

           Note that this test does not prevent a similar performance problem in a usecase where the tactic is used to synthesize a
           term that is not a proof. TODO: add better support for checking the delayed assignments. This is not high priority because
           tactics are usually only used for synthesizing proofs.
        -/
        match (← isDefEqProofIrrel t s) with
        | LBool.true => return LBool.true
        | LBool.false => return LBool.false
        | _ =>
          if tFn.isMVar || sFn.isMVar then
            let ctx ← read
            if ctx.config.isDefEqStuckEx then do
              trace[Meta.isDefEq.stuck] "{t} =?= {s}"
              Meta.throwIsDefEqStuck
            else
              return LBool.false
          else
            return LBool.undef
      else
        isDefEqQuickMVarMVar t s

/-- Both `t` and `s` are terms of the form `?m ...` -/
private partial def isDefEqQuickMVarMVar (t s : Expr) : MetaM LBool := do
  if s.isMVar && !t.isMVar then
     /- Solve `?m t =?= ?n` by trying first `?n := ?m t`.
        Reason: this assignment is precise. -/
     if (← checkpointDefEq (processAssignment s t)) then
       return LBool.true
     else
       toLBoolM <| processAssignment t s
  else
     if (← checkpointDefEq (processAssignment t s)) then
       return LBool.true
     else
       toLBoolM <| processAssignment s t

end

@[inline] def whenUndefDo (x : MetaM LBool) (k : MetaM Bool) : MetaM Bool := do
  let status ← x
  match status with
  | LBool.true  => pure true
  | LBool.false => pure false
  | LBool.undef => k

@[specialize] private def unstuckMVar (e : Expr) (successK : Expr → MetaM Bool) (failK : MetaM Bool): MetaM Bool := do
  match (← getStuckMVar? e) with
  | some mvarId =>
    trace[Meta.isDefEq.stuckMVar] "found stuck MVar {mkMVar mvarId} : {← inferType (mkMVar mvarId)}"
    if (← Meta.synthPending mvarId) then
      let e ← instantiateMVars e
      successK e
    else
      failK
  | none   => failK

private def isDefEqOnFailure (t s : Expr) : MetaM Bool := do
  withTraceNodeBefore `Meta.isDefEq.onFailure (return m!"{t} =?= {s}") do
    unstuckMVar t (fun t => Meta.isExprDefEqAux t s) <|
    unstuckMVar s (fun s => Meta.isExprDefEqAux t s) <|
    tryUnificationHints t s <||> tryUnificationHints s t

private def isDefEqProj : Expr → Expr → MetaM Bool
  | Expr.proj m i t, Expr.proj n j s => pure (i == j && m == n) <&&> Meta.isExprDefEqAux t s
  | Expr.proj structName 0 s, v => isDefEqSingleton structName s v
  | v, Expr.proj structName 0 s => isDefEqSingleton structName s v
  | _, _ => pure false
where
  /-- If `structName` is a structure with a single field and `(?m ...).1 =?= v`, then solve constraint as `?m ... =?= ⟨v⟩` -/
  isDefEqSingleton (structName : Name) (s : Expr) (v : Expr) : MetaM Bool := do
    if isClass (← getEnv) structName then
      /-
      We disable this feature if `structName` is a class. See issue #2011.
      The example at issue #2011, the following weird
      instance was being generated for `Zero (f x)`
      ```
      (@Zero.mk (f x✝) ((@instZero I (fun i => f i) fun i => inst✝¹ i).1 x✝)
      ```
      where `inst✝¹` is the local instance `[∀ i, Zero (f i)]`
      Note that this instance is definitionally equal to the expected nicer
      instance `inst✝¹ x✝`.
      However, the nasty instance trigger nasty unification higher order
      constraints later.

      We say this behavior is defensible because it is more reliable to use TC resolution to
      assign `?m`.
      -/
      return false
    let ctorVal := getStructureCtor (← getEnv) structName
    if ctorVal.numFields != 1 then
      return false -- It is not a structure with a single field.
    let sType ← whnf (← inferType s)
    let sTypeFn := sType.getAppFn
    if !sTypeFn.isConstOf structName then
      return false
    let s ← whnf s
    let sFn := s.getAppFn
    if !sFn.isMVar then
      return false
    if (← isAssignable sFn) then
      let ctorApp := mkApp (mkAppN (mkConst ctorVal.name sTypeFn.constLevels!) sType.getAppArgs) v
      processAssignment' s ctorApp
    else
      return false

/--
  Given applications `t` and `s` that are in WHNF (modulo the current transparency setting),
  check whether they are definitionally equal or not.
-/
private def isDefEqApp (t s : Expr) : MetaM Bool := do
  let tFn := t.getAppFn
  let sFn := s.getAppFn
  if tFn.isConst && sFn.isConst && tFn.constName! == sFn.constName! then
    /- See comment at `tryHeuristic` explaining why we process arguments before universe levels. -/
    if (← checkpointDefEq (isDefEqArgs tFn t.getAppArgs s.getAppArgs <&&> isListLevelDefEqAux tFn.constLevels! sFn.constLevels!)) then
      return true
    else
      isDefEqOnFailure t s
  else if (← checkpointDefEq (Meta.isExprDefEqAux tFn s.getAppFn <&&> isDefEqArgs tFn t.getAppArgs s.getAppArgs)) then
    return true
  else
    isDefEqOnFailure t s

/-- Return `true` if the type of the given expression is an inductive datatype with a single constructor with no fields. -/
private def isDefEqUnitLike (t : Expr) (s : Expr) : MetaM Bool := do
  let tType ← whnf (← inferType t)
  matchConstStruct tType.getAppFn (fun _ => return false) fun _ _ ctorVal => do
    if ctorVal.numFields != 0 then
      return false
    else if (← useEtaStruct ctorVal.induct) then
      Meta.isExprDefEqAux tType (← inferType s)
    else
      return false

/--
  The `whnf` procedure has support for unfolding class projections when the
  transparency mode is set to `.instances`. This method ensures the behavior
  of `whnf` and `isDefEq` is consistent in this transparency mode.
-/
private def isDefEqProjInst (t : Expr) (s : Expr) : MetaM LBool := do
  if (← getTransparency) != .instances then return .undef
  let t? ← unfoldProjInstWhenIntances? t
  let s? ← unfoldProjInstWhenIntances? s
  if t?.isSome || s?.isSome then
    toLBoolM <| Meta.isExprDefEqAux (t?.getD t) (s?.getD s)
  else
    return .undef

private def isExprDefEqExpensive (t : Expr) (s : Expr) : MetaM Bool := do
  whenUndefDo (isDefEqEta t s) do
  whenUndefDo (isDefEqEta s t) do
  if (← isDefEqProj t s) then return true
  whenUndefDo (isDefEqNative t s) do
  whenUndefDo (isDefEqNat t s) do
  whenUndefDo (isDefEqOffset t s) do
  whenUndefDo (isDefEqDelta t s) do
  -- We try structure eta *after* lazy delta reduction;
  -- otherwise we would end up applying it at every step of a reduction chain
  -- as soon as one of the sides is a constructor application,
  -- which is very costly because it requires us to unify the fields.
  if (← (isDefEqEtaStruct t s <||> isDefEqEtaStruct s t)) then
    return true
  if t.isConst && s.isConst then
    if t.constName! == s.constName! then isListLevelDefEqAux t.constLevels! s.constLevels! else return false
  else if (← pure t.isApp <&&> pure s.isApp <&&> isDefEqApp t s) then
    return true
  else
    whenUndefDo (isDefEqProjInst t s) do
    whenUndefDo (isDefEqStringLit t s) do
    if (← isDefEqUnitLike t s) then return true else
    isDefEqOnFailure t s

inductive DefEqCacheKind where
  | transient -- problem has mvars or is using nonstandard configuration, we should use transient cache
  | permanent -- problem does not have mvars and we are using standard config, we can use one persistent cache.

private def getDefEqCacheKind (t s : Expr) : MetaM DefEqCacheKind := do
  if t.hasMVar || s.hasMVar || (← read).canUnfold?.isSome then
    return .transient
  else
    return .permanent

/--
Structure for storing defeq cache key information.
-/
structure DefEqCacheKeyInfo where
  kind : DefEqCacheKind
  key  : Expr × Expr

private def mkCacheKey (t s : Expr) : MetaM DefEqCacheKeyInfo := do
  let kind ← getDefEqCacheKind t s
  let key := if Expr.quickLt t s then (t, s) else (s, t)
  return { key, kind }

private def getCachedResult (keyInfo : DefEqCacheKeyInfo) : MetaM LBool := do
  let cache ← match keyInfo.kind with
    | .transient => pure (← get).cache.defEqTrans
    | .permanent => pure (← get).cache.defEqPerm
  let cache := match (← getTransparency) with
    | .reducible => cache.reducible
    | .instances => cache.instances
    | .default   => cache.default
    | .all       => cache.all
  match cache.find? keyInfo.key with
  | some val => return val.toLBool
  | none => return .undef

def DefEqCache.update (cache : DefEqCache) (mode : TransparencyMode) (key : Expr × Expr) (result : Bool) : DefEqCache :=
  match mode with
  | .reducible => { cache with reducible := cache.reducible.insert key result }
  | .instances => { cache with instances := cache.instances.insert key result }
  | .default   => { cache with default   := cache.default.insert key result }
  | .all       => { cache with all       := cache.all.insert key result }

private def cacheResult (keyInfo : DefEqCacheKeyInfo) (result : Bool) : MetaM Unit := do
  let mode ← getTransparency
  let key := keyInfo.key
  match keyInfo.kind with
  | .permanent => modifyDefEqPermCache fun c => c.update mode key result
  | .transient =>
    /-
    We must ensure that all assigned metavariables in the key are replaced by their current assignments.
    Otherwise, the key is invalid after the assignment is "backtracked".
    See issue #1870 for an example.
    -/
    let key := (← instantiateMVars key.1, ← instantiateMVars key.2)
    modifyDefEqTransientCache fun c => c.update mode key result

@[export lean_is_expr_def_eq]
partial def isExprDefEqAuxImpl (t : Expr) (s : Expr) : MetaM Bool := withIncRecDepth do
  withTraceNodeBefore `Meta.isDefEq (return m!"{t} =?= {s}") do
  checkSystem "isDefEq"
  whenUndefDo (isDefEqQuick t s) do
  whenUndefDo (isDefEqProofIrrel t s) do
  /-
    We also reduce projections here to prevent expensive defeq checks when unifying TC operations.
    When unifying e.g. `@Neg.neg α (@Field.toNeg α inst1) =?= @Neg.neg α (@Field.toNeg α inst2)`,
    we only want to unify negation (and not all other field operations as well).
    Unifying the field instances slowed down unification: https://github.com/leanprover/lean4/issues/1986
    We used to *not* reduce projections here, to support unifying `(?a).1 =?= (x, y).1`.
    NOTE: this still seems to work because we don't eagerly unfold projection definitions to primitive projections.
  -/
  let t' ← whnfCore t
  let s' ← whnfCore s
  if t != t' || s != s' then
    isExprDefEqAuxImpl t' s'
  else
    /-
      TODO: check whether the following `instantiateMVar`s are expensive or not in practice.
      Lean 3 does not use them, and may miss caching opportunities since it is not safe to cache when `t` and `s` may contain mvars.
      The unit test `tryHeuristicPerfIssue2.lean` cannot be solved without these two `instantiateMVar`s.
      If it becomes a problem, we may use store a flag in the context indicating whether we have already used `instantiateMVar` in
      outer invocations or not. It is not perfect (we may assign mvars in nested calls), but it should work well enough in practice,
      and prevent repeated traversals in nested calls.
    -/
    let t ← instantiateMVars t
    let s ← instantiateMVars s
    let numPostponed ← getNumPostponed
    let k ← mkCacheKey t s
    match (← getCachedResult k) with
    | .true  =>
      trace[Meta.isDefEq.cache] "cache hit 'true' for {t} =?= {s}"
      return true
    | .false =>
      trace[Meta.isDefEq.cache] "cache hit 'false' for {t} =?= {s}"
      return false
    | .undef =>
      let result ← isExprDefEqExpensive t s
      if numPostponed == (← getNumPostponed) then
        trace[Meta.isDefEq.cache] "cache {result} for {t} =?= {s}"
        cacheResult k result
      return result

builtin_initialize
  registerTraceClass `Meta.isDefEq
  registerTraceClass `Meta.isDefEq.stuck
  registerTraceClass `Meta.isDefEq.stuckMVar (inherited := true)
  registerTraceClass `Meta.isDefEq.cache
  registerTraceClass `Meta.isDefEq.foApprox (inherited := true)
  registerTraceClass `Meta.isDefEq.onFailure (inherited := true)
  registerTraceClass `Meta.isDefEq.constApprox (inherited := true)
  registerTraceClass `Meta.isDefEq.delta
  registerTraceClass `Meta.isDefEq.delta.unfoldLeft (inherited := true)
  registerTraceClass `Meta.isDefEq.delta.unfoldRight (inherited := true)
  registerTraceClass `Meta.isDefEq.delta.unfoldLeftRight (inherited := true)
  registerTraceClass `Meta.isDefEq.assign
  registerTraceClass `Meta.isDefEq.assign.checkTypes (inherited := true)
  registerTraceClass `Meta.isDefEq.assign.outOfScopeFVar (inherited := true)
  registerTraceClass `Meta.isDefEq.assign.beforeMkLambda (inherited := true)
  registerTraceClass `Meta.isDefEq.assign.typeError (inherited := true)
  registerTraceClass `Meta.isDefEq.assign.occursCheck (inherited := true)
  registerTraceClass `Meta.isDefEq.assign.readOnlyMVarWithBiggerLCtx (inherited := true)
  registerTraceClass `Meta.isDefEq.eta.struct

end Lean.Meta
