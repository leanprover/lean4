/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Data.LBool
import Lean.Meta.Basic

namespace Lean

/--
Auxiliary function for instantiating the loose bound variables in `e` with `args[start:stop]`.
This function is similar to `instantiateRevRange`, but it applies beta-reduction when
we instantiate a bound variable with a lambda expression.
Example: Given the term `#0 a`, and `start := 0, stop := 1, args := #[fun x => x]` the result is
`a` instead of `(fun x => x) a`.
This reduction is useful when we are inferring the type of eliminator-like applications.
For example, given `(n m : Nat) (f : Nat → Nat) (h : m = n)`,
the type of `Eq.subst (motive := fun x => f m = f x) h rfl`
is `motive n` which is `(fun (x : Nat) => f m = f x) n`
This function reduces the new application to `f m = f n`

We use it to implement `inferAppType`
-/
partial def Expr.instantiateBetaRevRange (e : Expr) (start : Nat) (stop : Nat) (args : Array Expr) : Expr :=
  if e.hasLooseBVars && stop > start then
    assert! stop ≤ args.size
    visit e 0 |>.run
  else
    e
where
  visit (e : Expr) (offset : Nat) : MonadStateCacheT (ExprStructEq × Nat) Expr Id Expr :=
    if offset >= e.looseBVarRange then
      -- `e` doesn't have free variables
      return e
    else checkCache ({ val := e : ExprStructEq }, offset) fun _ => do
      match e with
      | .forallE _ d b _ => return e.updateForallE! (← visit d offset) (← visit b (offset+1))
      | .lam _ d b _     => return e.updateLambdaE! (← visit d offset) (← visit b (offset+1))
      | .letE _ t v b _  => return e.updateLet! (← visit t offset) (← visit v offset) (← visit b (offset+1))
      | .mdata _ b       => return e.updateMData! (← visit b offset)
      | .proj _ _ b      => return e.updateProj! (← visit b offset)
      | .app .. =>
        e.withAppRev fun f revArgs => do
        let fNew    ← visit f offset
        let revArgs ← revArgs.mapM (visit · offset)
        if f.isBVar then
          -- try to beta reduce if `f` was a bound variable
          return fNew.betaRev revArgs
        else
          return mkAppRev fNew revArgs
      | Expr.bvar vidx         =>
        -- Recall that looseBVarRange for `Expr.bvar` is `vidx+1`.
        -- So, we must have offset ≤ vidx, since we are in the "else" branch of  `if offset >= e.looseBVarRange`
        let n := stop - start
        if vidx < offset + n then
          return args[stop - (vidx - offset) - 1]!.liftLooseBVars 0 offset
        else
          return mkBVar (vidx - n)
      -- The following cases are unreachable because they never contain loose bound variables
      | .const .. => unreachable!
      | .fvar ..  => unreachable!
      | .mvar ..  => unreachable!
      | .sort ..  => unreachable!
      | .lit ..   => unreachable!

namespace Meta

def throwFunctionExpected {α} (f : Expr) : MetaM α :=
  throwError "function expected{indentExpr f}"

private def inferAppType (f : Expr) (args : Array Expr) : MetaM Expr := do
  let mut fType ← inferType f
  let mut j := 0
  /- TODO: check whether `instantiateBetaRevRange` is too expensive, and
     use it only when `args` contains a lambda expression. -/
  for i in [:args.size] do
    match fType with
    | Expr.forallE _ _ b _ => fType := b
    | _ =>
      match (← whnf <| fType.instantiateBetaRevRange j i args) with
      | Expr.forallE _ _ b _ => j := i; fType := b
      | _ => throwFunctionExpected <| mkAppRange f 0 (i+1) args
  return fType.instantiateBetaRevRange j args.size args

def throwIncorrectNumberOfLevels {α} (constName : Name) (us : List Level) : MetaM α :=
  throwError "incorrect number of universe levels {mkConst constName us}"

private def inferConstType (c : Name) (us : List Level) : MetaM Expr := do
  let cinfo ← getConstInfo c
  if cinfo.levelParams.length == us.length then
    instantiateTypeLevelParams cinfo us
  else
    throwIncorrectNumberOfLevels c us

private def inferProjType (structName : Name) (idx : Nat) (e : Expr) : MetaM Expr := do
  let structType ← inferType e
  let structType ← whnf structType
  let failed {α} : Unit → MetaM α := fun _ => do
    throwError "invalid projection{indentExpr (mkProj structName idx e)}\nfrom type{indentExpr structType}"
  matchConstStructure structType.getAppFn failed fun structVal structLvls ctorVal => do
    unless structVal.name == structName do
      failed ()
    let structTypeArgs := structType.getAppArgs
    if structVal.numParams + structVal.numIndices != structTypeArgs.size then
      failed ()
    else do
      let mut ctorType ← inferAppType (mkConst ctorVal.name structLvls) structTypeArgs[:structVal.numParams]
      for i in [:idx] do
        ctorType ← whnf ctorType
        match ctorType with
        | .forallE _ _ body _ =>
          if body.hasLooseBVars then
            ctorType := body.instantiate1 <| mkProj structName i e
          else
            ctorType := body
        | _ => failed ()
      ctorType ← whnf ctorType
      match ctorType with
      | .forallE _ d _ _ => return d.consumeTypeAnnotations
      | _                => failed ()

def throwTypeExcepted {α} (type : Expr) : MetaM α :=
  throwError "type expected{indentExpr type}"

def getLevel (type : Expr) : MetaM Level := do
  let typeType ← inferType type
  let typeType ← whnfD typeType
  match typeType with
  | Expr.sort lvl     => return lvl
  | Expr.mvar mvarId  =>
    if (← mvarId.isReadOnlyOrSyntheticOpaque) then
      throwTypeExcepted type
    else
      let lvl ← mkFreshLevelMVar
      mvarId.assign (mkSort lvl)
      return lvl
  | _ => throwTypeExcepted type

private def inferForallType (e : Expr) : MetaM Expr :=
  forallTelescope e fun xs e => do
    let lvl  ← getLevel e
    let lvl  ← xs.foldrM (init := lvl) fun x lvl => do
      let xType    ← inferType x
      let xTypeLvl ← getLevel xType
      return mkLevelIMax' xTypeLvl lvl
    return mkSort lvl.normalize

/-- Infer type of lambda and let expressions -/
private def inferLambdaType (e : Expr) : MetaM Expr :=
  lambdaLetTelescope e fun xs e => do
    let type ← inferType e
    mkForallFVars xs type

def throwUnknownMVar {α} (mvarId : MVarId) : MetaM α :=
  throwError "unknown metavariable '?{mvarId.name}'"

private def inferMVarType (mvarId : MVarId) : MetaM Expr := do
  match (← getMCtx).findDecl? mvarId with
  | some d => return d.type
  | none   => throwUnknownMVar mvarId

private def inferFVarType (fvarId : FVarId) : MetaM Expr := do
  match (← getLCtx).find? fvarId with
  | some d => return d.type
  | none   => fvarId.throwUnknown

@[inline] private def checkInferTypeCache (e : Expr) (inferType : MetaM Expr) : MetaM Expr := do
  if e.hasMVar then
    inferType
  else
    let key ← mkExprConfigCacheKey e
    match (← get).cache.inferType.find? key with
    | some type => return type
    | none =>
      let type ← inferType
      unless type.hasMVar do
        modifyInferTypeCache fun c => c.insert key type
      return type

/--
Ensure `MetaM` configuration is strong enough for inferring/checking types.
For example, `beta := true` is essential when type checking.

Remark: we previously use the default configuration here, but this is problematic
because it overrides unrelated configurations.
-/
@[inline] def withInferTypeConfig (x : MetaM α) : MetaM α :=
  withAtLeastTransparency .default do
    let cfg ← getConfig
    if cfg.beta && cfg.iota && cfg.zeta && cfg.zetaDelta && cfg.proj == .yesWithDelta then
      x
    else
      withConfig (fun cfg => { cfg with beta := true, iota := true, zeta := true, zetaDelta := true, proj := .yesWithDelta }) x

@[export lean_infer_type]
def inferTypeImp (e : Expr) : MetaM Expr :=
  let rec infer (e : Expr) :  MetaM Expr := do
    match e with
    | .const c []    => inferConstType c []
    | .const c us    => checkInferTypeCache e (inferConstType c us)
    | .proj n i s    => checkInferTypeCache e (inferProjType n i s)
    | .app f ..      => checkInferTypeCache e (inferAppType f.getAppFn e.getAppArgs)
    | .mvar mvarId   => inferMVarType mvarId
    | .fvar fvarId   => inferFVarType fvarId
    | .bvar bidx     => throwError "unexpected bound variable {mkBVar bidx}"
    | .mdata _ e     => infer e
    | .lit v         => return v.type
    | .sort lvl      => return mkSort (mkLevelSucc lvl)
    | .forallE ..    => checkInferTypeCache e (inferForallType e)
    | .lam ..        => checkInferTypeCache e (inferLambdaType e)
    | .letE ..       => checkInferTypeCache e (inferLambdaType e)
  withIncRecDepth <| withInferTypeConfig (infer e)

/--
  Return `LBool.true` if given level is always equivalent to universe level zero.
  It is used to implement `isProp`. -/
private def isAlwaysZero : Level → Bool
  | .zero ..    => true
  | .mvar ..    => false
  | .param ..   => false
  | .succ ..    => false
  | .max u v    => isAlwaysZero u && isAlwaysZero v
  | .imax _ u   => isAlwaysZero u

/--
  `isArrowProp type n` is an "approximate" predicate which returns `LBool.true`
   if `type` is of the form `A_1 -> ... -> A_n -> Prop`.
   Remark: `type` can be a dependent arrow. -/
private partial def isArrowProp : Expr → Nat → MetaM LBool
  | .sort u,          0   => return isAlwaysZero (← instantiateLevelMVars u) |>.toLBool
  | .forallE ..,      0   => return LBool.false
  | .forallE _ _ b _, n+1 => isArrowProp b n
  | .letE _ _ _ b _,  n   => isArrowProp b n
  | .mdata _ e,       n   => isArrowProp e n
  | _,                _   => return LBool.undef

/--
  `isPropQuickApp f n` is an "approximate" predicate which returns `LBool.true`
   if `f` applied to `n` arguments is a proposition. -/
private partial def isPropQuickApp : Expr → Nat → MetaM LBool
  | .const c lvls,   arity   => do let constType ← inferConstType c lvls; isArrowProp constType arity
  | .fvar fvarId,    arity   => do let fvarType  ← inferFVarType fvarId;  isArrowProp fvarType arity
  | .mvar mvarId,    arity   => do let mvarType  ← inferMVarType mvarId;  isArrowProp mvarType arity
  | .app f ..,       arity   => isPropQuickApp f (arity+1)
  | .mdata _ e,      arity   => isPropQuickApp e arity
  | .letE _ _ _ b _, arity   => isPropQuickApp b arity
  | .lam ..,         0       => return LBool.false
  | .lam _ _ b _,    arity+1 => isPropQuickApp b arity
  | _,               _       => return LBool.undef

/--
  `isPropQuick e` is an "approximate" predicate which returns `LBool.true`
  if `e` is a proposition. -/
partial def isPropQuick : Expr → MetaM LBool
  | .bvar ..          => return LBool.undef
  | .lit ..           => return LBool.false
  | .sort ..          => return LBool.false
  | .lam ..           => return LBool.false
  | .letE _ _ _ b _   => isPropQuick b
  | .proj ..          => return LBool.undef
  | .forallE _ _ b _  => isPropQuick b
  | .mdata _ e        => isPropQuick e
  | .const c lvls     => do let constType ← inferConstType c lvls; isArrowProp constType 0
  | .fvar fvarId      => do let fvarType  ← inferFVarType fvarId;  isArrowProp fvarType 0
  | .mvar mvarId      => do let mvarType  ← inferMVarType mvarId;  isArrowProp mvarType 0
  | .app f ..         => isPropQuickApp f 1

/-- `isProp e` returns `true` if `e` is a proposition.

     If `e` contains metavariables, it may not be possible
     to decide whether is a proposition or not. We return `false` in this
     case. We considered using `LBool` and retuning `LBool.undef`, but
     we have no applications for it. -/
def isProp (e : Expr) : MetaM Bool := do
  match (← isPropQuick e) with
  | .true  => return true
  | .false => return false
  | .undef =>
    let type ← inferType e
    let type ← whnfD type
    match type with
    | Expr.sort u => return isAlwaysZero (← instantiateLevelMVars u)
    | _           => return false

/--
  `isArrowProposition type n` is an "approximate" predicate which returns `LBool.true`
   if `type` is of the form `A_1 -> ... -> A_n -> B`, where `B` is a proposition.
   Remark: `type` can be a dependent arrow. -/
private partial def isArrowProposition : Expr → Nat → MetaM LBool
  | .forallE _ _ b _, n+1 => isArrowProposition b n
  | .letE _ _ _ b _,  n   => isArrowProposition b n
  | .mdata _ e,       n   => isArrowProposition e n
  | type,             0   => isPropQuick type
  | _,                _   => return LBool.undef

mutual
/--
  `isProofQuickApp f n` is an "approximate" predicate which returns `LBool.true`
   if `f` applied to `n` arguments is a proof. -/
private partial def isProofQuickApp : Expr → Nat → MetaM LBool
  | .const c lvls,   arity   => do let constType ← inferConstType c lvls; isArrowProposition constType arity
  | .fvar fvarId,    arity   => do let fvarType  ← inferFVarType fvarId;  isArrowProposition fvarType arity
  | .mvar mvarId,    arity   => do let mvarType  ← inferMVarType mvarId;  isArrowProposition mvarType arity
  | .app f _,        arity   => isProofQuickApp f (arity+1)
  | .mdata _ e,      arity   => isProofQuickApp e arity
  | .letE _ _ _ b _, arity   => isProofQuickApp b arity
  | .lam _ _ b _,    0       => isProofQuick b
  | .lam _ _ b _,    arity+1 => isProofQuickApp b arity
  | _,               _       => return LBool.undef

/--
  `isProofQuick e` is an "approximate" predicate which returns `LBool.true`
  if `e` is a proof. -/
partial def isProofQuick : Expr → MetaM LBool
  | .bvar ..          => return LBool.undef
  | .lit ..           => return LBool.false
  | .sort ..          => return LBool.false
  | .lam _ _ b _      => isProofQuick b
  | .letE _ _ _ b _   => isProofQuick b
  | .proj ..          => return LBool.undef
  | .forallE ..       => return LBool.false
  | .mdata _ e        => isProofQuick e
  | .const c lvls     => do let constType ← inferConstType c lvls; isArrowProposition constType 0
  | .fvar fvarId      => do let fvarType  ← inferFVarType fvarId;  isArrowProposition fvarType 0
  | .mvar mvarId      => do let mvarType  ← inferMVarType mvarId;  isArrowProposition mvarType 0
  | .app f ..         => isProofQuickApp f 1

end

def isProof (e : Expr) : MetaM Bool := do
  match (← isProofQuick e) with
  | .true  => return true
  | .false => return false
  | .undef => Meta.isProp (← inferType e)

/--
  `isArrowType type n` is an "approximate" predicate which returns `LBool.true`
   if `type` is of the form `A_1 -> ... -> A_n -> Sort _`.
   Remark: `type` can be a dependent arrow. -/
private partial def isArrowType : Expr → Nat → MetaM LBool
  | .sort ..,         0   => return LBool.true
  | .forallE ..,      0   => return LBool.false
  | .forallE _ _ b _, n+1 => isArrowType b n
  | .letE _ _ _ b _,  n   => isArrowType b n
  | .mdata _ e,       n   => isArrowType e n
  | _,                _   => return LBool.undef

/--
  `isTypeQuickApp f n` is an "approximate" predicate which returns `LBool.true`
   if `f` applied to `n` arguments is a type. -/
private partial def isTypeQuickApp : Expr → Nat → MetaM LBool
  | .const c lvls,   arity   => do let constType ← inferConstType c lvls; isArrowType constType arity
  | .fvar fvarId,    arity   => do let fvarType  ← inferFVarType fvarId;  isArrowType fvarType arity
  | .mvar mvarId,    arity   => do let mvarType  ← inferMVarType mvarId;  isArrowType mvarType arity
  | .app f _,        arity   => isTypeQuickApp f (arity+1)
  | .mdata _ e,      arity   => isTypeQuickApp e arity
  | .letE _ _ _ b _, arity   => isTypeQuickApp b arity
  | .lam ..,         0       => return LBool.false
  | .lam _ _ b _,    arity+1 => isTypeQuickApp b arity
  | _,               _       => return LBool.undef

/--
  `isTypeQuick e` is an "approximate" predicate which returns `LBool.true`
  if `e` is a type. -/
partial def isTypeQuick : Expr → MetaM LBool
  | .bvar ..          => return LBool.undef
  | .lit ..           => return LBool.false
  | .sort ..          => return LBool.true
  | .lam ..           => return LBool.false
  | .letE _ _ _ b _   => isTypeQuick b
  | .proj ..          => return LBool.undef
  | .forallE ..       => return LBool.true
  | .mdata _ e        => isTypeQuick e
  | .const c lvls     => do let constType ← inferConstType c lvls; isArrowType constType 0
  | .fvar fvarId      => do let fvarType  ← inferFVarType fvarId;  isArrowType fvarType 0
  | .mvar mvarId      => do let mvarType  ← inferMVarType mvarId;  isArrowType mvarType 0
  | .app f ..         => isTypeQuickApp f 1

/--
Return `true` iff the type of `e` is a `Sort _`.
-/
def isType (e : Expr) : MetaM Bool := do
  match (← isTypeQuick e) with
  | .true  => return true
  | .false => return false
  | .undef =>
    let type ← inferType e
    let type ← whnfD type
    match type with
    | .sort .. => return true
    | _        => return false

def typeFormerTypeLevelQuick : Expr → Option Level
  | .forallE _ _ b _ => typeFormerTypeLevelQuick b
  | .sort l => some l
  | _ => none

/--
Return `u` iff `type` is `Sort u` or `As → Sort u`.
-/
partial def typeFormerTypeLevel (type : Expr) : MetaM (Option Level) := do
  match typeFormerTypeLevelQuick type with
  | .some l => return .some l
  | .none => savingCache <| go type #[]
where
  go (type : Expr) (xs : Array Expr) : MetaM (Option Level) := do
    match type with
    | .sort l => return some l
    | .forallE n d b c => withLocalDeclNoLocalInstanceUpdate n c (d.instantiateRev xs) fun x => go b (xs.push x)
    | _ =>
      let type ← whnfD (type.instantiateRev xs)
      match type with
      | .sort l => return some l
      | .forallE .. => go type #[]
      | _ => return none

/--
Return true iff `type` is `Sort _` or `As → Sort _`.
-/
partial def isTypeFormerType (type : Expr) : MetaM Bool := do
  return (← typeFormerTypeLevel type).isSome

/--
Return true iff `type` is `Prop` or `As → Prop`.
-/
partial def isPropFormerType (type : Expr) : MetaM Bool := do
  return (← typeFormerTypeLevel type) == .some .zero

/--
Return true iff `e : Sort _` or `e : (forall As, Sort _)`.
Remark: it subsumes `isType`
-/
def isTypeFormer (e : Expr) : MetaM Bool := do
  isTypeFormerType (← inferType e)


/--
Given `n` and a non-dependent function type `α₁ → α₂ → ... → αₙ → Sort u`, returns the
types `α₁, α₂, ..., αₙ`. Throws an error if there are not at least `n` argument types or if a
later argument type depends on a prior one (i.e., it's a dependent function type).

This can be used to infer the expected type of the alternatives when constructing a `MatcherApp`.
-/
def arrowDomainsN (n : Nat) (type : Expr) : MetaM (Array Expr) := do
  forallBoundedTelescope type n fun xs _ => do
    unless xs.size = n do
      throwError "type {type} does not have {n} parameters"
    let types ← xs.mapM (inferType ·)
    for t in types do
      if t.hasAnyFVar (fun fvar => xs.contains (.fvar fvar)) then
        throwError "unexpected dependent type {t} in {type}"
    return types

/--
Infers the types of the next `n` parameters that `e` expects. See `arrowDomainsN`.
-/
def inferArgumentTypesN (n : Nat) (e : Expr) : MetaM (Array Expr) := do
  arrowDomainsN n (← inferType e)

end Lean.Meta
