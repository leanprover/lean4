/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.ToExpr
import Lean.AuxRecursor
import Lean.Meta.Basic
import Lean.Meta.LevelDefEq

namespace Lean.Meta

/- ===========================
   Smart unfolding support
   =========================== -/

def smartUnfoldingSuffix := "_sunfold"

@[inline] def mkSmartUnfoldingNameFor (n : Name) : Name :=
  mkNameStr n smartUnfoldingSuffix

/- ===========================
   Helper methods
   =========================== -/
variables {m : Type → Type} [MonadLiftT MetaM m]

private def isAuxDefImp? (constName : Name) : MetaM Bool := do
  let env ← getEnv
  pure (isAuxRecursor env constName || isNoConfusion env constName)

@[inline] def isAuxDef? (constName : Name) : m Bool :=
  liftMetaM $ isAuxDefImp? constName

@[inline] private def matchConstAux {α} (e : Expr) (failK : Unit → MetaM α) (k : ConstantInfo → List Level → MetaM α) : MetaM α :=
  match e with
  | Expr.const name lvls _ => do
    let (some cinfo) ← getConst? name | failK ()
    k cinfo lvls
  | _ => failK ()

/- ===========================
   Helper functions for reducing recursors
   =========================== -/

private def getFirstCtor (d : Name) : MetaM (Option Name) := do
  let some (ConstantInfo.inductInfo { ctors := ctor::_, ..}) ← getConstNoEx? d | pure none
  pure (some ctor)

private def mkNullaryCtor (type : Expr) (nparams : Nat) : MetaM (Option Expr) :=
  match type.getAppFn with
  | Expr.const d lvls _ => do
    let (some ctor) ← getFirstCtor d | pure none
    pure $ mkAppN (mkConst ctor lvls) (type.getAppArgs.shrink nparams)
  | _ => pure none

def toCtorIfLit : Expr → Expr
  | Expr.lit (Literal.natVal v) _ =>
    if v == 0 then mkConst `Nat.zero
    else mkApp (mkConst `Nat.succ) (mkNatLit (v-1))
  | Expr.lit (Literal.strVal v) _ =>
    mkApp (mkConst `String.mk) (toExpr v.toList)
  | e => e

private def getRecRuleFor (recVal : RecursorVal) (major : Expr) : Option RecursorRule :=
  match major.getAppFn with
  | Expr.const fn _ _ => recVal.rules.find? $ fun r => r.ctor == fn
  | _                 => none

private def toCtorWhenK (recVal : RecursorVal) (major : Expr) : MetaM (Option Expr) := do
  let majorType ← inferType major
  let majorType ← whnf majorType
  let majorTypeI := majorType.getAppFn
  if !majorTypeI.isConstOf recVal.getInduct then
    pure none
  else if majorType.hasExprMVar && majorType.getAppArgs[recVal.nparams:].any Expr.hasExprMVar then
    pure none
  else do
    let (some newCtorApp) ← mkNullaryCtor majorType recVal.nparams | pure none
    let newType ← inferType newCtorApp
    if (← isDefEq majorType newType) then
      pure newCtorApp
    else
      pure none

/-- Auxiliary function for reducing recursor applications. -/
private def reduceRec {α} (recVal : RecursorVal) (recLvls : List Level) (recArgs : Array Expr) (failK : Unit → MetaM α) (successK : Expr → MetaM α) : MetaM α :=
  let majorIdx := recVal.getMajorIdx
  if h : majorIdx < recArgs.size then do
    let major := recArgs.get ⟨majorIdx, h⟩
    let major ← whnf major
    if recVal.k then
      let newMajor ← toCtorWhenK recVal major
      major := newMajor.getD major
    let major := toCtorIfLit major
    match getRecRuleFor recVal major with
    | some rule =>
      let majorArgs := major.getAppArgs
      if recLvls.length != recVal.lparams.length then
        failK ()
      else
        let rhs := rule.rhs.instantiateLevelParams recVal.lparams recLvls
        -- Apply parameters, motives and minor premises from recursor application.
        let rhs := mkAppRange rhs 0 (recVal.nparams+recVal.nmotives+recVal.nminors) recArgs
        /- The number of parameters in the constructor is not necessarily
           equal to the number of parameters in the recursor when we have
           nested inductive types. -/
        let nparams := majorArgs.size - rule.nfields
        let rhs := mkAppRange rhs nparams majorArgs.size majorArgs
        let rhs := mkAppRange rhs (majorIdx + 1) recArgs.size recArgs
        successK rhs
    | none => failK ()
  else
    failK ()

@[specialize] private def isRecStuck? (isStuck? : Expr → MetaM (Option MVarId)) (recVal : RecursorVal) (recLvls : List Level) (recArgs : Array Expr)
    : MetaM (Option MVarId) :=
  if recVal.k then
    -- TODO: improve this case
    pure none
  else do
    let majorIdx := recVal.getMajorIdx
    if h : majorIdx < recArgs.size then do
      let major := recArgs.get ⟨majorIdx, h⟩
      major ← whnf major
      isStuck? major
    else
      pure none

/- ===========================
   Helper functions for reducing Quot.lift and Quot.ind
   =========================== -/

/-- Auxiliary function for reducing `Quot.lift` and `Quot.ind` applications. -/
private def reduceQuotRec {α} (recVal  : QuotVal) (recLvls : List Level) (recArgs : Array Expr) (failK : Unit → MetaM α) (successK : Expr → MetaM α) : MetaM α :=
  let process (majorPos argPos : Nat) : MetaM α :=
    if h : majorPos < recArgs.size then do
      let major := recArgs.get ⟨majorPos, h⟩
      major ← whnf major
      match major with
      | Expr.app (Expr.app (Expr.app (Expr.const majorFn _ _) _ _) _ _) majorArg _ => do
        let some (ConstantInfo.quotInfo { kind := QuotKind.ctor, .. }) ← getConstNoEx? majorFn | failK ()
        let f := recArgs[argPos]
        let r := mkApp f majorArg
        let recArity := majorPos + 1
        successK $ mkAppRange r recArity recArgs.size recArgs
      | _ => failK ()
    else
      failK ()
  match recVal.kind with
  | QuotKind.lift => process 5 3
  | QuotKind.ind  => process 4 3
  | _             => failK ()

@[specialize] private def isQuotRecStuck? (isStuck? : Expr → MetaM (Option MVarId)) (recVal : QuotVal) (recLvls : List Level) (recArgs : Array Expr)
    : MetaM (Option MVarId) :=
  let process? (majorPos : Nat) : MetaM (Option MVarId) :=
    if h : majorPos < recArgs.size then do
      let major := recArgs.get ⟨majorPos, h⟩
      major ← whnf major
      isStuck? major
    else
      pure none
  match recVal.kind with
  | QuotKind.lift => process? 5
  | QuotKind.ind  => process? 4
  | _             => pure none

/- ===========================
   Helper function for extracting "stuck term"
   =========================== -/

/-- Return `some (Expr.mvar mvarId)` if metavariable `mvarId` is blocking reduction. -/
private partial def getStuckMVarImp? : Expr → MetaM (Option MVarId)
  | Expr.mdata _ e _       => getStuckMVarImp? e
  | Expr.proj _ _ e _      => do getStuckMVarImp? (← whnf e)
  | e@(Expr.mvar mvarId _) => pure (some mvarId)
  | e@(Expr.app f _ _) =>
    let f := f.getAppFn
    match f with
    | Expr.mvar mvarId _       => pure (some mvarId)
    | Expr.const fName fLvls _ => do
      let cinfo? ← getConstNoEx? fName
      match cinfo? with
      | some $ ConstantInfo.recInfo recVal  => isRecStuck? getStuckMVarImp? recVal fLvls e.getAppArgs
      | some $ ConstantInfo.quotInfo recVal => isQuotRecStuck? getStuckMVarImp? recVal fLvls e.getAppArgs
      | _                                => pure none
    | _ => pure none
  | _ => pure none

@[inline] def getStuckMVar? (e : Expr) : m (Option MVarId) :=
  liftM $ getStuckMVarImp? e

/- ===========================
   Weak Head Normal Form auxiliary combinators
   =========================== -/

/-- Auxiliary combinator for handling easy WHNF cases. It takes a function for handling the "hard" cases as an argument -/
@[specialize] private partial def whnfEasyCases : Expr → (Expr → MetaM Expr) → MetaM Expr
  | e@(Expr.forallE _ _ _ _), _ => pure e
  | e@(Expr.lam _ _ _ _),     _ => pure e
  | e@(Expr.sort _ _),        _ => pure e
  | e@(Expr.lit _ _),         _ => pure e
  | e@(Expr.bvar _ _),        _ => unreachable!
  | Expr.mdata _ e _,         k => whnfEasyCases e k
  | e@(Expr.letE _ _ _ _ _),  k => k e
  | e@(Expr.fvar fvarId _),   k => do
    let decl ← getLocalDecl fvarId
    match decl with
    | LocalDecl.cdecl _ _ _ _ _        => pure e
    | LocalDecl.ldecl _ _ _ _ v nonDep =>
      let cfg ← getConfig
      if nonDep && !cfg.zetaNonDep then
        pure e
      else
        when cfg.trackZeta do
          modify fun s => { s with zetaFVarIds := s.zetaFVarIds.insert fvarId }
        whnfEasyCases v k
  | e@(Expr.mvar mvarId _),   k => do
    match (← getExprMVarAssignment? mvarId) with
    | some v => whnfEasyCases v k
    | none   => pure e
  | e@(Expr.const _ _ _),     k => k e
  | e@(Expr.app _ _ _),       k => k e
  | e@(Expr.proj _ _ _ _),    k => k e

/-- Return true iff term is of the form `idRhs ...` -/
private def isIdRhsApp (e : Expr) : Bool :=
  e.isAppOf `idRhs

/-- (@idRhs T f a_1 ... a_n) ==> (f a_1 ... a_n) -/
private def extractIdRhs (e : Expr) : Expr :=
  if !isIdRhsApp e then e
  else
    let args := e.getAppArgs
    if args.size < 2 then e
    else mkAppRange args[1] 2 args.size args

@[specialize] private def deltaDefinition {α} (c : ConstantInfo) (lvls : List Level)
    (failK : Unit → α) (successK : Expr → α) : α :=
  if c.lparams.length != lvls.length then failK ()
  else
    let val := c.instantiateValueLevelParams lvls
    successK (extractIdRhs val)

@[specialize] private def deltaBetaDefinition {α} (c : ConstantInfo) (lvls : List Level) (revArgs : Array Expr)
    (failK : Unit → α) (successK : Expr → α) : α :=
  if c.lparams.length != lvls.length then failK ()
  else
    let val := c.instantiateValueLevelParams lvls
    let val := val.betaRev revArgs
    successK (extractIdRhs val)

/--
  Apply beta-reduction, zeta-reduction (i.e., unfold let local-decls), iota-reduction,
  expand let-expressions, expand assigned meta-variables. -/
private partial def whnfCoreImp (e : Expr) : MetaM Expr :=
  whnfEasyCases e fun e => do
    trace[Meta.whnf]! e
    match e with
    | e@(Expr.const _ _ _)    => pure e
    | e@(Expr.letE _ _ v b _) => whnfCoreImp $ b.instantiate1 v
    | e@(Expr.app f _ _)      =>
      let f := f.getAppFn
      let f' ← whnfCoreImp f
      if f'.isLambda then
        let revArgs := e.getAppRevArgs
        whnfCoreImp $ f'.betaRev revArgs
      else
        let done : Unit → MetaM Expr := fun _ =>
          if f == f' then pure e else pure $ e.updateFn f'
        matchConstAux f' done fun cinfo lvls =>
          match cinfo with
          | ConstantInfo.recInfo rec    => reduceRec rec lvls e.getAppArgs done whnfCoreImp
          | ConstantInfo.quotInfo rec   => reduceQuotRec rec lvls e.getAppArgs done whnfCoreImp
          | c@(ConstantInfo.defnInfo _) => do
            let unfold? ← isAuxDef? c.name
            if unfold? then
              deltaBetaDefinition c lvls e.getAppRevArgs done whnfCoreImp
            else
              done ()
          | _ => done ()
    | e@(Expr.proj _ i c _) =>
      let c   ← whnf c
      matchConstAux c.getAppFn (fun _ => pure e) fun cinfo lvls =>
        match cinfo with
        | ConstantInfo.ctorInfo ctorVal =>
          let argIdx := ctorVal.nparams + i
          if argIdx < c.getAppNumArgs then
            whnfCoreImp $ c.getArg! argIdx
          else
            pure e
        | _ => pure e
    | _ => unreachable!

@[inline] def whnfCore (e : Expr) : m Expr :=
  liftMetaM $ whnfCoreImp e

/--
  Similar to `whnfCore`, but uses `synthesizePending` to (try to) synthesize metavariables
  that are blocking reduction. -/
private partial def whnfCoreUnstuck (e : Expr) : MetaM Expr := do
  let e ← whnfCore e
  let (some mvarId) ← getStuckMVar? e | pure e
  let succeeded     ← Meta.synthPending mvarId
  if succeeded then whnfCoreUnstuck e else pure e

/-- Unfold definition using "smart unfolding" if possible. -/
private def unfoldDefinitionImp? (e : Expr) : MetaM (Option Expr) :=
  match e with
  | Expr.app f _ _ =>
    matchConstAux f.getAppFn (fun _ => pure none) $ fun fInfo fLvls =>
      if fInfo.lparams.length != fLvls.length then pure none
      else do
        let fAuxInfo? ← getConstNoEx? (mkSmartUnfoldingNameFor fInfo.name)
        match fAuxInfo? with
        | some $ fAuxInfo@(ConstantInfo.defnInfo _) =>
          deltaBetaDefinition fAuxInfo fLvls e.getAppRevArgs (fun _ => pure none) $ fun e₁ => do
            let e₂ ← whnfCoreUnstuck e₁
            if isIdRhsApp e₂ then
              pure (some (extractIdRhs e₂))
            else
              pure none
        | _ =>
          if fInfo.hasValue then
            deltaBetaDefinition fInfo fLvls e.getAppRevArgs (fun _ => pure none) (fun e => pure (some e))
          else
            pure none
  | Expr.const name lvls _ => do
    let (some (cinfo@(ConstantInfo.defnInfo _))) ← getConstNoEx? name | pure none
    deltaDefinition cinfo lvls (fun _ => pure none) (fun e => pure (some e))
  | _ => pure none

@[inline] def unfoldDefinition? (e : Expr) : m (Option Expr) :=
  liftMetaM $ unfoldDefinitionImp? e

unsafe def reduceBoolNativeUnsafe (constName : Name) : MetaM Bool := evalConstCheck Bool `Bool constName
unsafe def reduceNatNativeUnsafe (constName : Name) : MetaM Nat := evalConstCheck Nat `Nat constName
@[implementedBy reduceBoolNativeUnsafe] constant reduceBoolNative (constName : Name) : MetaM Bool := arbitrary _
@[implementedBy reduceNatNativeUnsafe] constant reduceNatNative (constName : Name) : MetaM Nat := arbitrary _

def reduceNative? (e : Expr) : MetaM (Option Expr) :=
  match e with
  | Expr.app (Expr.const fName _ _) (Expr.const argName _ _) _ =>
    if fName == `Lean.reduceBool then do
      let b ← reduceBoolNative argName
      pure $ toExpr b
    else if fName == `Lean.reduceNat then do
      let n ← reduceNatNative argName
      pure $ toExpr n
    else
      pure none
  | _ => pure none

@[inline] def withNatValue {α} (a : Expr) (k : Nat → MetaM (Option α)) : MetaM (Option α) := do
  let a ← whnf a
  match a with
  | Expr.const `Nat.zero _ _      => k 0
  | Expr.lit (Literal.natVal v) _ => k v
  | _                             => pure none

def reduceUnaryNatOp (f : Nat → Nat) (a : Expr) : MetaM (Option Expr) :=
  withNatValue a fun a =>
  pure $ mkNatLit $ f a

def reduceBinNatOp (f : Nat → Nat → Nat) (a b : Expr) : MetaM (Option Expr) :=
  withNatValue a fun a =>
  withNatValue b fun b => do
  trace[Meta.isDefEq.whnf.reduceBinOp]! "{a} op {b}"
  pure $ mkNatLit $ f a b

def reduceBinNatPred (f : Nat → Nat → Bool) (a b : Expr) : MetaM (Option Expr) := do
  withNatValue a fun a =>
  withNatValue b fun b =>
  pure $ toExpr $ f a b

def reduceNat? (e : Expr) : MetaM (Option Expr) :=
  if e.hasFVar || e.hasMVar then
    pure none
  else match e with
    | Expr.app (Expr.const fn _ _) a _                  =>
      if fn == `Nat.succ then reduceUnaryNatOp Nat.succ a
      else pure none
    | Expr.app (Expr.app (Expr.const fn _ _) a1 _) a2 _ =>
      if fn == `Nat.add then reduceBinNatOp Nat.add a1 a2
      else if fn == `Nat.sub then reduceBinNatOp Nat.sub a1 a2
      else if fn == `Nat.mul then reduceBinNatOp Nat.mul a1 a2
      else if fn == `Nat.div then reduceBinNatOp Nat.div a1 a2
      else if fn == `Nat.mod then reduceBinNatOp Nat.mod a1 a2
      else if fn == `Nat.beq then reduceBinNatPred Nat.beq a1 a2
      else if fn == `Nat.ble then reduceBinNatPred Nat.ble a1 a2
      else pure none
    | _ => pure none


@[inline] private def useWHNFCache (e : Expr) : MetaM Bool := do
  -- We cache only closed terms without expr metavars.
  -- Potential refinement: cache if `e` is not stuck at a metavariable
  if e.hasFVar || e.hasExprMVar then
    pure false
  else
    let ctx ← read
    pure $ ctx.config.transparency != TransparencyMode.reducible

@[inline] private def cached? (useCache : Bool) (e : Expr) : MetaM (Option Expr) := do
  if useCache then
    let ctx ← read
    let s   ← get
    match ctx.config.transparency with
    | TransparencyMode.default => pure $ s.cache.whnfDefault.find? e
    | TransparencyMode.all     => pure $ s.cache.whnfAll.find? e
    | _                        => unreachable!
  else
    pure none

private def cache (useCache : Bool) (e r : Expr) : MetaM Expr := do
  let ctx ← read
  if useCache then
    match ctx.config.transparency with
    | TransparencyMode.default => modify fun s => { s with cache := { s.cache with whnfDefault := s.cache.whnfDefault.insert e r } }
    | TransparencyMode.all     => modify fun s => { s with cache := { s.cache with whnfAll := s.cache.whnfAll.insert e r } }
    | _                        => unreachable!
  pure r

partial def whnfImp (e : Expr) : MetaM Expr :=
  whnfEasyCases e fun e => do
    let useCache ← useWHNFCache e
    match (← cached? useCache e) with
    | some e' => pure e'
    | none    =>
      let e' ← whnfCore e
      match (← reduceNat? e') with
      | some v => cache useCache e v
      | none   =>
        match (← reduceNative? e') with
        | some v => cache useCache e v
        | none   =>
          match (← unfoldDefinition? e') with
          | some e => whnfImp e
          | none   => cache useCache e e'

@[builtinInit] def setWHNFRef : IO Unit :=
  whnfRef.set whnfImp

/- Given an expression `e`, compute its WHNF and if the result is a constructor, return field #i. -/
def reduceProj? (e : Expr) (i : Nat) : MetaM (Option Expr) := do
  let e ← whnf e
  matchConstCtor e.getAppFn (fun _ => pure none) fun ctorVal _ =>
    let numArgs := e.getAppNumArgs
    let idx := ctorVal.nparams + i
    if idx < numArgs then
      pure (some (e.getArg! idx))
    else
      pure none

@[specialize] partial def whnfHeadPredImp (e : Expr) (pred : Expr → MetaM Bool) : MetaM Expr :=
  whnfEasyCases e fun e => do
    let e ← whnfCore e
    if (← pred e) then
        match (← unfoldDefinition? e) with
        | some e => whnfHeadPredImp e pred
        | none   => pure e
    else
      pure e

@[inline] def whnfHeadPred (e : Expr) (pred : Expr → MetaM Bool) : m Expr :=
  liftMetaM $ whnfHeadPredImp e pred

def whnfUntil (e : Expr) (declName : Name) : m (Option Expr) := liftMetaM do
  let e ← whnfHeadPredImp e (fun e => pure $ !e.isAppOf declName)
  if e.isAppOf declName then pure e
  else pure none

builtin_initialize
  registerTraceClass `Meta.whnf

end Lean.Meta
