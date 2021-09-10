/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.ProjFns
import Lean.Structure
import Lean.Meta.WHNF
import Lean.Meta.InferType
import Lean.Meta.FunInfo
import Lean.Meta.LevelDefEq
import Lean.Meta.Check
import Lean.Meta.Offset
import Lean.Meta.ForEachExpr
import Lean.Meta.UnificationHint

namespace Lean.Meta

/--
  Try to solve `a := (fun x => t) =?= b` by eta-expanding `b`.

  Remark: eta-reduction is not a good alternative even in a system without universe cumulativity like Lean.
  Example:
    ```
    (fun x : A => f ?m) =?= f
    ```
    The left-hand side of the constraint above it not eta-reduced because `?m` is a metavariable. -/
private def isDefEqEta (a b : Expr) : MetaM Bool := do
  if a.isLambda && !b.isLambda then
    let bType ← inferType b
    let bType ← whnfD bType
    match bType with
    | Expr.forallE n d _ c =>
      let b' := mkLambda n c.binderInfo d (mkApp b (mkBVar 0))
      checkpointDefEq <| Meta.isExprDefEqAux a b'
    | _ => pure false
  else
    pure false

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
  if s.isStringLit && t.isAppOf `String.mk then
    isDefEq (toCtorIfLit s) t
  else if s.isAppOf `String.mk && t.isStringLit then
    isDefEq s (toCtorIfLit t)
  else
    pure LBool.undef

/--
  Return `true` if `e` is of the form `fun (x_1 ... x_n) => ?m x_1 ... x_n)`, and `?m` is unassigned.
  Remark: `n` may be 0. -/
def isEtaUnassignedMVar (e : Expr) : MetaM Bool := do
  match e.etaExpanded? with
  | some (Expr.mvar mvarId _) =>
    if (← isReadOnlyOrSyntheticOpaqueExprMVar mvarId) then
      pure false
    else if (← isExprMVarAssigned mvarId) then
      pure false
    else
      pure true
  | _   => pure false

/-
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
-/
private partial def isDefEqArgsFirstPass
    (paramInfo : Array ParamInfo) (args₁ args₂ : Array Expr) : MetaM (Option (Array Nat)) := do
  let rec loop (i : Nat) (postponed : Array Nat) := do
    if h : i < paramInfo.size then
      let info := paramInfo.get ⟨i, h⟩
      let a₁ := args₁[i]
      let a₂ := args₂[i]
      if !info.isExplicit then
        if (← isEtaUnassignedMVar a₁ <||> isEtaUnassignedMVar a₂) then
          if (← Meta.isExprDefEqAux a₁ a₂) then
            loop (i+1) postponed
          else
            pure none
        else
          loop (i+1) (postponed.push i)
      else if (← Meta.isExprDefEqAux a₁ a₂) then
        loop (i+1) postponed
      else
        pure none
    else
      pure (some postponed)
  loop 0 #[]

@[specialize] private def trySynthPending (e : Expr) : MetaM Bool := do
  let mvarId? ← getStuckMVar? e
  match mvarId? with
  | some mvarId => Meta.synthPending mvarId
  | none        => pure false

private partial def isDefEqArgs (f : Expr) (args₁ args₂ : Array Expr) : MetaM Bool :=
  if h : args₁.size = args₂.size then do
    let finfo ← getFunInfoNArgs f args₁.size
    let (some postponed) ← isDefEqArgsFirstPass finfo.paramInfo args₁ args₂ | pure false
    let rec processOtherArgs (i : Nat) : MetaM Bool := do
      if h₁ : i < args₁.size then
        let a₁ := args₁.get ⟨i, h₁⟩
        let a₂ := args₂.get ⟨i, Eq.subst h h₁⟩
        if (← Meta.isExprDefEqAux a₁ a₂) then
          processOtherArgs (i+1)
        else
          pure false
      else
        pure true
    if (← processOtherArgs finfo.paramInfo.size) then
      postponed.allM fun i => do
        /- Second pass: unify implicit arguments.
           In the second pass, we make sure we are unfolding at
           least non reducible definitions (default setting). -/
        let a₁   := args₁[i]
        let a₂   := args₂[i]
        let info := finfo.paramInfo[i]
        if info.isInstImplicit then
          discard <| trySynthPending a₁
          discard <| trySynthPending a₂
        withAtLeastTransparency TransparencyMode.default <| Meta.isExprDefEqAux a₁ a₂
    else
      pure false
  else
    pure false

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
      let d₂       := ds₂[i]
      if (← Meta.isExprDefEqAux fvarType d₂) then
        match (← isClass? fvarType) with
        | some className => withNewLocalInstance className fvar <| loop (i+1)
        | none           => loop (i+1)
      else
        pure false
    else
      k
  loop 0

/- Auxiliary function for `isDefEqBinding` for handling binders `forall/fun`.
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
  traceCtx `Meta.isDefEq.assign.checkTypes do
    if !mvar.isMVar then
      trace[Meta.isDefEq.assign.final] "metavariable expected at {mvar} := {v}"
      return false
    else
      -- must check whether types are definitionally equal or not, before assigning and returning true
      let mvarType ← inferType mvar
      let vType ← inferType v
      if (← withTransparency TransparencyMode.default <| Meta.isExprDefEqAux mvarType vType) then
        trace[Meta.isDefEq.assign.final] "{mvar} := {v}"
        assignExprMVar mvar.mvarId! v
        pure true
      else
        trace[Meta.isDefEq.assign.typeMismatch] "{mvar} : {mvarType} := {v} : {vType}"
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
    trace[Meta.debug] "ys: {ys}, v: {v}"
    mkLambdaFVars ys v

where
  /- Return true if there are let-declarions between `xs[0]` and `xs[xs.size-1]`.
     We use it a quick-check to avoid the more expensive collection procedure. -/
  hasLetDeclsInBetween : MetaM Bool := do
    let check (lctx : LocalContext) : Bool := do
      let start := lctx.getFVar! xs[0] |>.index
      let stop  := lctx.getFVar! xs.back |>.index
      for i in [start+1:stop] do
        match lctx.getAt? i with
        | some localDecl =>
          if localDecl.isLet then
            return true
        | _ => pure ()
      return false
    if xs.size <= 1 then
      pure false
    else
      check (← getLCtx)

  /- Traverse `e` and stores in the state `NameHashSet` any let-declaration with index greater than `(← read)`.
     The context `Nat` is the position of `xs[0]` in the local context. -/
  collectLetDeclsFrom (e : Expr) : ReaderT Nat (StateRefT FVarIdHashSet MetaM) Unit := do
    let rec visit (e : Expr) : MonadCacheT Expr Unit (ReaderT Nat (StateRefT FVarIdHashSet MetaM)) Unit :=
      checkCache e fun _ => do
        match e with
        | Expr.forallE _ d b _   => visit d; visit b
        | Expr.lam _ d b _       => visit d; visit b
        | Expr.letE _ t v b _    => visit t; visit v; visit b
        | Expr.app f a _         => visit f; visit a
        | Expr.mdata _ b _       => visit b
        | Expr.proj _ _ b _      => visit b
        | Expr.fvar fvarId _     =>
          let localDecl ← getLocalDecl fvarId
          if localDecl.isLet && localDecl.index > (← read) then
            modify fun s => s.insert localDecl.fvarId
        | _ => pure ()
    visit (← instantiateMVars e) |>.run

  /-
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

  /- Computes the set `ys`. It is a set of `FVarId`s, -/
  collectLetDeps : MetaM FVarIdHashSet := do
    let lctx ← getLCtx
    let start := lctx.getFVar! xs[0] |>.index
    let stop  := lctx.getFVar! xs.back |>.index
    let s := xs.foldl (init := {}) fun s x => s.insert x.fvarId!
    let (_, s) ← collectLetDepsAux stop |>.run start |>.run s
    return s

  /- Computes the array `ys` containing let-decls between `xs[0]` and `xs.back` that
     some `x` in `xs` depends on. -/
  addLetDeps : MetaM (Array Expr) := do
    let lctx ← getLCtx
    let s ← collectLetDeps
    /- Convert `s` into the array `ys` -/
    let start := lctx.getFVar! xs[0] |>.index
    let stop  := lctx.getFVar! xs.back |>.index
    let mut ys := #[]
    for i in [start:stop+1] do
      match lctx.getAt? i with
      | none => pure ()
      | some localDecl =>
        if s.contains localDecl.fvarId then
          ys := ys.push localDecl.toExpr
    return ys

/-
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
     (approximated) solution (when `config.ctxApprox` is set to true) :
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
     In this example, the following unification contraint is generated.
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
     We distinguish the two cases above by using the field `numScopeArgs` at `MetavarDecl`. This fiels tracks
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

@[inline] private def visit (f : Expr → CheckAssignmentM Expr) (e : Expr) : CheckAssignmentM Expr :=
  if !e.hasExprMVar && !e.hasFVar then pure e else checkCache e (fun _ => f e)

private def addAssignmentInfo (msg : MessageData) : CheckAssignmentM MessageData := do
  let ctx ← read
  return m!"{msg} @ {mkMVar ctx.mvarId} {ctx.fvars} := {ctx.rhs}"

@[inline] def run (x : CheckAssignmentM Expr) (mvarId : MVarId) (fvars : Array Expr) (hasCtxLocals : Bool) (v : Expr) : MetaM (Option Expr) := do
  let mvarDecl ← getMVarDecl mvarId
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
      | some (LocalDecl.ldecl (value := v) ..) => visit check v
      | _ =>
        if ctx.fvars.contains fvar then pure fvar
        else
          traceM `Meta.isDefEq.assign.outOfScopeFVar do addAssignmentInfo fvar
          throwOutOfScopeFVar

  partial def checkMVar (mvar : Expr) : CheckAssignmentM Expr := do
    let mvarId := mvar.mvarId!
    let ctx  ← read
    let mctx ← getMCtx
    if mvarId == ctx.mvarId then
      traceM `Meta.isDefEq.assign.occursCheck <| addAssignmentInfo "occurs check failed"
      throwCheckAssignmentFailure
    else match mctx.getExprAssignment? mvarId with
      | some v => check v
      | none   =>
        match mctx.findDecl? mvarId with
        | none          => throwUnknownMVar mvarId
        | some mvarDecl =>
          if ctx.hasCtxLocals then
            throwCheckAssignmentFailure -- It is not a pattern, then we fail and fall back to FO unification
          else if mvarDecl.lctx.isSubPrefixOf ctx.mvarDecl.lctx ctx.fvars then
            /- The local context of `mvar` - free variables being abstracted is a subprefix of the metavariable being assigned.
               We "substract" variables being abstracted because we use `elimMVarDeps` -/
            pure mvar
          else if mvarDecl.depth != mctx.depth || mvarDecl.kind.isSyntheticOpaque then
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
              let toErase := mvarDecl.lctx.foldl (init := #[]) fun toErase localDecl =>
                if ctx.mvarDecl.lctx.contains localDecl.fvarId then
                  toErase
                else if ctx.fvars.any fun fvar => fvar.fvarId! == localDecl.fvarId then
                  if mctx.findLocalDeclDependsOn localDecl fun fvarId => toErase.contains fvarId then
                    -- localDecl depends on a variable that will be erased. So, we must add it to `toErase` too
                    toErase.push localDecl.fvarId
                  else
                    toErase
                else
                  toErase.push localDecl.fvarId
              let lctx := toErase.foldl (init := mvarDecl.lctx) fun lctx toEraseFVar =>
                lctx.erase toEraseFVar
              /- Compute new set of local instances. -/
              let localInsts := mvarDecl.localInstances.filter fun localInst => toErase.contains localInst.fvar.fvarId!
              let mvarType ← check mvarDecl.type
              let newMVar ← mkAuxMVar lctx localInsts mvarType mvarDecl.numScopeArgs
              modifyThe Meta.State fun s => { s with mctx := s.mctx.assignExpr mvarId newMVar }
              pure newMVar
            else
              traceM `Meta.isDefEq.assign.readOnlyMVarWithBiggerLCtx <| addAssignmentInfo (mkMVar mvarId)
              throwCheckAssignmentFailure

  /-
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
        let f ← visit checkMVar f
        catchInternalId outOfScopeExceptionId
          (do
            let args ← args.mapM (visit check)
            return mkAppN f args)
          (fun ex => do
            if !f.isMVar then
              throw ex
            else if (← isDelayedAssigned f.mvarId!) then
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
        let f ← visit check f
        let args ← args.mapM (visit check)
        return mkAppN f args

  partial def check (e : Expr) : CheckAssignmentM Expr := do
    match e with
    | Expr.mdata _ b _     => return e.updateMData! (← visit check b)
    | Expr.proj _ _ s _    => return e.updateProj! (← visit check s)
    | Expr.lam _ d b _     => return e.updateLambdaE! (← visit check d) (← visit check b)
    | Expr.forallE _ d b _ => return e.updateForallE! (← visit check d) (← visit check b)
    | Expr.letE _ t v b _  => return e.updateLet! (← visit check t) (← visit check v) (← visit check b)
    | Expr.bvar ..         => return e
    | Expr.sort ..         => return e
    | Expr.const ..        => return e
    | Expr.lit ..          => return e
    | Expr.fvar ..         => visit checkFVar e
    | Expr.mvar ..         => visit checkMVar e
    | Expr.app ..          =>
      checkApp e
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
    (hasCtxLocals ctxApprox : Bool)
    (mctx : MetavarContext) (lctx : LocalContext) (mvarDecl : MetavarDecl) (mvarId : MVarId) (fvars : Array Expr) (e : Expr) : Bool :=
  let rec visit (e : Expr) : Bool :=
    if !e.hasExprMVar && !e.hasFVar then
      true
    else match e with
    | Expr.mdata _ b _     => visit b
    | Expr.proj _ _ s _    => visit s
    | Expr.app f a _       => visit f && visit a
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
        | some (LocalDecl.ldecl (value := v) ..) => false -- need expensive CheckAssignment.check
        | _ =>
          if fvars.any fun x => x.fvarId! == fvarId then true
          else false -- We could throw an exception here, but we would have to use ExceptM. So, we let CheckAssignment.check do it
    | Expr.mvar mvarId' _  =>
      match mctx.getExprAssignment? mvarId' with
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
    let mvarDecl ← getMVarDecl mvarId
    let hasCtxLocals := fvars.any fun fvar => mvarDecl.lctx.containsFVar fvar
    let ctx ← read
    let mctx ← getMCtx
    if CheckAssignmentQuick.check hasCtxLocals ctx.config.ctxApprox mctx ctx.lctx mvarDecl mvarId fvars v then
      pure (some v)
    else
      let v ← instantiateMVars v
      CheckAssignment.checkAssignmentAux mvarId fvars hasCtxLocals v

private def processAssignmentFOApproxAux (mvar : Expr) (args : Array Expr) (v : Expr) : MetaM Bool :=
  match v with
  | Expr.app f a _ =>
    if args.isEmpty then
      pure false
    else
      Meta.isExprDefEqAux args.back a <&&> Meta.isExprDefEqAux (mkAppRange mvar 0 (args.size - 1) args) f
  | _              => pure false

/-
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

private partial def simpAssignmentArgAux : Expr → MetaM Expr
  | Expr.mdata _ e _       => simpAssignmentArgAux e
  | e@(Expr.fvar fvarId _) => do
    let decl ← getLocalDecl fvarId
    match decl.value? with
    | some value => simpAssignmentArgAux value
    | _          => pure e
  | e => pure e

/- Auxiliary procedure for processing `?m a₁ ... aₙ =?= v`.
   We apply it to each `aᵢ`. It instantiates assigned metavariables if `aᵢ` is of the form `f[?n] b₁ ... bₘ`,
   and then removes metadata, and zeta-expand let-decls. -/
private def simpAssignmentArg (arg : Expr) : MetaM Expr := do
  let arg ← if arg.getAppFn.hasExprMVar then instantiateMVars arg else pure arg
  simpAssignmentArgAux arg

/- Assign `mvar := fun a_1 ... a_{numArgs} => v`.
   We use it at `processConstApprox` and `isDefEqMVarSelf` -/
private def assignConst (mvar : Expr) (numArgs : Nat) (v : Expr) : MetaM Bool := do
  let mvarDecl ← getMVarDecl mvar.mvarId!
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

private def processConstApprox (mvar : Expr) (numArgs : Nat) (v : Expr) : MetaM Bool := do
  let cfg ← getConfig
  let mvarId := mvar.mvarId!
  let mvarDecl ← getMVarDecl mvarId
  if mvarDecl.numScopeArgs == numArgs || cfg.constApprox then
    assignConst mvar numArgs v
  else
    pure false

/-- Tries to solve `?m a₁ ... aₙ =?= v` by assigning `?m`.
    It assumes `?m` is unassigned. -/
private partial def processAssignment (mvarApp : Expr) (v : Expr) : MetaM Bool :=
  traceCtx `Meta.isDefEq.assign do
    trace[Meta.isDefEq.assign] "{mvarApp} := {v}"
    let mvar := mvarApp.getAppFn
    let mvarDecl ← getMVarDecl mvar.mvarId!
    let rec process (i : Nat) (args : Array Expr) (v : Expr) := do
      let cfg ← getConfig
      let useFOApprox (args : Array Expr) : MetaM Bool :=
        processAssignmentFOApprox mvar args v <||> processConstApprox mvar args.size v
      if h : i < args.size then
        let arg := args.get ⟨i, h⟩
        let arg ← simpAssignmentArg arg
        let args := args.set ⟨i, h⟩ arg
        match arg with
        | Expr.fvar fvarId _ =>
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
  | Expr.const c _ _ =>
    match (← getConst? c) with
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
  /- We only use the heuristic when `f` is a regular definition. That is, it is marked an abbreviation
     (e.g., a user-facing projection) or as opaque (e.g., proof).
     We check whether terms contain metavariables to make sure we can solve constraints such
     as `S.proj ?x =?= S.proj t` without performing delta-reduction.
     That is, we are assuming the heuristic implemented by this method is seldom effective
     when `t` and `s` do not have metavariables, are not structurally equal, and `f` is an abbreviation.
     On the other hand, by unfolding `f`, we often produce smaller terms. -/
  unless info.hints.isRegular do
    unless t.hasExprMVar || s.hasExprMVar do
      return false
  traceCtx `Meta.isDefEq.delta do
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
      let b ← isDefEqArgs tFn t.getAppArgs s.getAppArgs
              <&&>
              isListLevelDefEqAux tFn.constLevels! sFn.constLevels!
      unless b do
        trace[Meta.isDefEq.delta] "heuristic failed {t} =?= {s}"
      pure b

/-- Auxiliary method for isDefEqDelta -/
private abbrev unfold (e : Expr) (failK : MetaM α) (successK : Expr → MetaM α) : MetaM α := do
  match (← unfoldDefinition? e) with
  | some e => successK e
  | none   => failK

/-- Auxiliary method for isDefEqDelta -/
private def unfoldBothDefEq (fn : Name) (t s : Expr) : MetaM LBool := do
  match t, s with
  | Expr.const _ ls₁ _, Expr.const _ ls₂ _ => isListLevelDefEq ls₁ ls₂
  | Expr.app _ _ _,     Expr.app _ _ _     =>
    if (← tryHeuristic t s) then
      pure LBool.true
    else
      unfold t
       (unfold s (pure LBool.false) (fun s => isDefEqRight fn t s))
       (fun t => unfold s (isDefEqLeft fn t s) (fun s => isDefEqLeftRight fn t s))
  | _, _ => pure LBool.false

private def sameHeadSymbol (t s : Expr) : Bool :=
  match t.getAppFn, s.getAppFn with
  | Expr.const c₁ _ _, Expr.const c₂ _ _ => true
  | _,                 _                 => false

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
  If `t` is a projection function application and `s` is not ==> `isDefEqRight t (unfold s)`
  If `s` is a projection function application and `t` is not ==> `isDefEqRight (unfold t) s`

  Otherwise, use `unfoldReducibeDefEq`

  Auxiliary method for isDefEqDelta -/
private def unfoldNonProjFnDefEq (tInfo sInfo : ConstantInfo) (t s : Expr) : MetaM LBool := do
  let tProj? ← isProjectionFn tInfo.name
  let sProj? ← isProjectionFn sInfo.name
  if tProj? && !sProj? then
    unfold s (unfoldDefEq tInfo sInfo t s) fun s => isDefEqRight sInfo.name t s
  else if !tProj? && sProj? then
    unfold t (unfoldDefEq tInfo sInfo t s) fun t => isDefEqLeft tInfo.name t s
  else
    unfoldReducibeDefEq tInfo sInfo t s

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
  let tInfo? ← isDeltaCandidate? t.getAppFn
  let sInfo? ← isDeltaCandidate? s.getAppFn
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
  | Expr.mvar mvarId _ => isExprMVarAssigned mvarId
  | _                  => pure false

private def isDelayedAssignedHead (tFn : Expr) (t : Expr) : MetaM Bool := do
  match tFn with
  | Expr.mvar mvarId _ =>
    if (← isDelayedAssigned mvarId) then
      let tNew ← instantiateMVars t
      return tNew != t
    else
      pure false
  | _ => pure false

private def isSynthetic : Expr → MetaM Bool
  | Expr.mvar mvarId _ => do
    let mvarDecl ← getMVarDecl mvarId
    match mvarDecl.kind with
    | MetavarKind.synthetic       => pure true
    | MetavarKind.syntheticOpaque => pure true
    | MetavarKind.natural         => pure false
  | _                  => pure false

private def isAssignable : Expr → MetaM Bool
  | Expr.mvar mvarId _ => do let b ← isReadOnlyOrSyntheticOpaqueExprMVar mvarId; pure (!b)
  | _                  => pure false

private def etaEq (t s : Expr) : Bool :=
  match t.etaExpanded? with
  | some t => t == s
  | none   => false

private def isLetFVar (fvarId : FVarId) : MetaM Bool := do
  let decl ← getLocalDecl fvarId
  pure decl.isLet

private def isDefEqProofIrrel (t s : Expr) : MetaM LBool := do
  if (← getConfig).proofIrrelevance then
    let status ← isProofQuick t
    match status with
    | LBool.false =>
      pure LBool.undef
    | LBool.true  =>
      let tType ← inferType t
      let sType ← inferType s
      toLBoolM <| Meta.isExprDefEqAux tType sType
    | LBool.undef =>
      let tType ← inferType t
      if (← isProp tType) then
        let sType ← inferType s
        toLBoolM <| Meta.isExprDefEqAux tType sType
      else
        pure LBool.undef
  else
    pure LBool.undef

/- Try to solve constraint of the form `?m args₁ =?= ?m args₂`.
   - First try to unify `args₁` and `args₂`, and return true if successful
   - Otherwise, try to assign `?m` to a constant function of the form `fun x_1 ... x_n => ?n`
     where `?n` is a fresh metavariable. See `processConstApprox`. -/
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
    let mvarDecl ← getMVarDecl mvarId
    if mvarDecl.numScopeArgs == args₁.size || cfg.constApprox then
      let type ← inferType (mkAppN mvar args₁)
      let auxMVar ← mkAuxMVar mvarDecl.lctx mvarDecl.localInstances type
      assignConst mvar args₁.size auxMVar
    else
      pure false

/- Remove unnecessary let-decls -/
private def consumeLet : Expr → Expr
  | e@(Expr.letE _ _ _ b _) => if b.hasLooseBVars then e else consumeLet b
  | e                       => e

mutual

private partial def isDefEqQuick (t s : Expr) : MetaM LBool :=
  let t := consumeLet t
  let s := consumeLet s
  match t, s with
  | Expr.lit  l₁ _,      Expr.lit l₂ _       => return (l₁ == l₂).toLBool
  | Expr.sort u _,       Expr.sort v _       => toLBoolM <| isLevelDefEqAux u v
  | Expr.lam ..,         Expr.lam ..         => if t == s then pure LBool.true else toLBoolM <| isDefEqBinding t s
  | Expr.forallE ..,     Expr.forallE ..     => if t == s then pure LBool.true else toLBoolM <| isDefEqBinding t s
  | Expr.mdata _ t _,    s                   => isDefEqQuick t s
  | t,                   Expr.mdata _ s _    => isDefEqQuick t s
  | Expr.fvar fvarId₁ _, Expr.fvar fvarId₂ _ => do
    if (← isLetFVar fvarId₁ <||> isLetFVar fvarId₂) then
      pure LBool.undef
    else if fvarId₁ == fvarId₂ then
      pure LBool.true
    else
      isDefEqProofIrrel t s
  | t, s =>
    isDefEqQuickOther t s

private partial def isDefEqQuickOther (t s : Expr) : MetaM LBool := do
  if t == s then
    pure LBool.true
  else if etaEq t s || etaEq s t then
    pure LBool.true  -- t =?= (fun xs => t xs)
  else
    let tFn := t.getAppFn
    let sFn := s.getAppFn
    if !tFn.isMVar && !sFn.isMVar then
      pure LBool.undef
    else if (← isAssigned tFn) then
      let t ← instantiateMVars t
      isDefEqQuick t s
    else if (← isAssigned sFn) then
      let s ← instantiateMVars s
      isDefEqQuick t s
    else if (← isDelayedAssignedHead tFn t) then
      let t ← instantiateMVars t
      isDefEqQuick t s
    else if (← isDelayedAssignedHead sFn s) then
      let s ← instantiateMVars s
      isDefEqQuick t s
    /- Remark: we do not eagerly synthesize synthetic metavariables when the constraint is not stuck.
       Reason: we may fail to solve a constraint of the form `?x =?= A` when the synthesized instance
       is not definitionally equal to `A`. We left the code here as a remainder of this issue. -/
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
        if tFn.isMVar || sFn.isMVar then
          let ctx ← read
          if ctx.config.isDefEqStuckEx then do
            trace[Meta.isDefEq.stuck] "{t} =?= {s}"
            Meta.throwIsDefEqStuck
          else
            pure LBool.false
        else
          pure LBool.undef
      else
        isDefEqQuickMVarMVar t s

-- Both `t` and `s` are terms of the form `?m ...`
private partial def isDefEqQuickMVarMVar (t s : Expr) : MetaM LBool := do
  let tFn := t.getAppFn
  let sFn := s.getAppFn
  let tMVarDecl ← getMVarDecl tFn.mvarId!
  let sMVarDecl ← getMVarDecl sFn.mvarId!
  if s.isMVar && !t.isMVar then
     /- Solve `?m t =?= ?n` by trying first `?n := ?m t`.
        Reason: this assignment is precise. -/
     if (← checkpointDefEq (processAssignment s t)) then
       pure LBool.true
     else
       toLBoolM <| processAssignment t s
  else
     if (← checkpointDefEq (processAssignment t s)) then
       pure LBool.true
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
  trace[Meta.isDefEq.onFailure] "{t} =?= {s}"
  unstuckMVar t (fun t => Meta.isExprDefEqAux t s) <|
  unstuckMVar s (fun s => Meta.isExprDefEqAux t s) <|
  tryUnificationHints t s <||> tryUnificationHints s t

private def isDefEqProj : Expr → Expr → MetaM Bool
  | Expr.proj _ i t _, Expr.proj _ j s _ => pure (i == j) <&&> Meta.isExprDefEqAux t s
  | Expr.proj structName 0 s _, v => isDefEqSingleton structName s v
  | v, Expr.proj structName 0 s _ => isDefEqSingleton structName s v
  | _, _ => pure false
where
  /- If `structName` is a structure with a single field, then reduce `s.1 =?= v` to `s =?= ⟨v⟩` -/
  isDefEqSingleton (structName : Name) (s : Expr) (v : Expr) : MetaM Bool := do
    let ctorVal := getStructureCtor (← getEnv) structName
    if ctorVal.numFields != 1 then
      return false -- It is not a structure with a single field.
    let sType ← whnf (← inferType s)
    let sTypeFn := sType.getAppFn
    if !sTypeFn.isConstOf structName then
      return false
    let ctorApp := mkApp (mkAppN (mkConst ctorVal.name sTypeFn.constLevels!) sType.getAppArgs) v
    Meta.isExprDefEqAux s ctorApp

/-
  Given applications `t` and `s` that are in WHNF (modulo the current transparency setting),
  check whether they are definitionally equal or not.
-/
private def isDefEqApp (t s : Expr) : MetaM Bool := do
  let tFn := t.getAppFn
  let sFn := s.getAppFn
  if tFn.isConst && sFn.isConst && tFn.constName! == sFn.constName! then
    /- See comment at `tryHeuristic` explaining why we processe arguments before universe levels. -/
    if (← checkpointDefEq (isDefEqArgs tFn t.getAppArgs s.getAppArgs <&&> isListLevelDefEqAux tFn.constLevels! sFn.constLevels!)) then
      return true
    else
      isDefEqOnFailure t s
  else if (← checkpointDefEq (Meta.isExprDefEqAux tFn s.getAppFn <&&> isDefEqArgs tFn t.getAppArgs s.getAppArgs)) then
    return true
  else
    isDefEqOnFailure t s

private def isExprDefEqExpensive (t : Expr) (s : Expr) : MetaM Bool := do
  if (← (isDefEqEta t s <||> isDefEqEta s t)) then pure true else
  if (← isDefEqProj t s) then pure true else
  whenUndefDo (isDefEqNative t s) do
  whenUndefDo (isDefEqNat t s) do
  whenUndefDo (isDefEqOffset t s) do
  whenUndefDo (isDefEqDelta t s) do
  if t.isConst && s.isConst then
    if t.constName! == s.constName! then isListLevelDefEqAux t.constLevels! s.constLevels! else pure false
  else if t.isApp && s.isApp then
    isDefEqApp t s
  else
    whenUndefDo (isDefEqStringLit t s) do
    isDefEqOnFailure t s

-- We only check DefEq cache for default and all transparency modes
private def skipDefEqCache : MetaM Bool := do
  match (← getConfig).transparency with
  | TransparencyMode.default => return false
  | TransparencyMode.all     => return false
  | _                        => return true

private def mkCacheKey (t : Expr) (s : Expr) : Expr × Expr :=
  if Expr.quickLt t s then (t, s) else (s, t)

private def isCached (key : Expr × Expr) : MetaM Bool := do
  match (← getConfig).transparency with
  | TransparencyMode.default => return (← get).cache.defEqDefault.contains key
  | TransparencyMode.all     => return (← get).cache.defEqAll.contains key
  | _                        => return false

private def cacheResult (key : Expr × Expr) : MetaM Unit := do
  match (← getConfig).transparency with
  | TransparencyMode.default => modify fun s => { s with cache.defEqDefault := s.cache.defEqDefault.insert key () }
  | TransparencyMode.all     => modify fun s => { s with cache.defEqAll := s.cache.defEqAll.insert key () }
  | _                        => pure ()


@[export lean_is_expr_def_eq]
partial def isExprDefEqAuxImpl (t : Expr) (s : Expr) : MetaM Bool := withIncRecDepth do
  trace[Meta.isDefEq.step] "{t} =?= {s}"
  checkMaxHeartbeats "isDefEq"
  withNestedTraces do
  whenUndefDo (isDefEqQuick t s) do
  whenUndefDo (isDefEqProofIrrel t s) do
  let t' ← whnfCore t
  let s' ← whnfCore s
  if t != t' || s != s' then
    isExprDefEqAuxImpl t' s'
  else if (← skipDefEqCache) then
    isExprDefEqExpensive t s
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
    if t.hasMVar || s.hasMVar then
      -- It is not safe to use DefEq cache if terms contain metavariables
      isExprDefEqExpensive t s
    else
      let k := mkCacheKey t s
      if (← isCached k) then
        return true
      else if (← isExprDefEqExpensive t s) then
        cacheResult k
        return true
      else
        return false

builtin_initialize
  registerTraceClass `Meta.isDefEq
  registerTraceClass `Meta.isDefEq.foApprox
  registerTraceClass `Meta.isDefEq.constApprox
  registerTraceClass `Meta.isDefEq.delta
  registerTraceClass `Meta.isDefEq.step
  registerTraceClass `Meta.isDefEq.assign

end Lean.Meta
