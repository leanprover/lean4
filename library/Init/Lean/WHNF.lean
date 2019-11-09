/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Lean.Declaration
import Init.Lean.LocalContext

namespace Lean
/- ===========================
   Smart unfolding support
   =========================== -/

def smartUnfoldingSuffix := "_sunfold"

@[inline] def mkSmartUnfoldingNameFor (n : Name) : Name :=
Name.mkString n smartUnfoldingSuffix

/- ===========================
   Helper functions
   =========================== -/

@[inline]
def matchConstAux {α : Type} {m : Type → Type} [Monad m]
    (getConst : Name → m (Option ConstantInfo))
    (e : Expr) (failK : Unit → m α) (k : ConstantInfo → List Level → m α) : m α :=
match e with
| Expr.const name lvls => do
  (some cinfo) ← getConst name | failK ();
  k cinfo lvls
| _ => failK ()

/- ===========================
   Helper functions for reducing recursors
   =========================== -/

private def getFirstCtor {m : Type → Type} [Monad m]
   (getConst : Name → m (Option ConstantInfo))
   (d : Name) : m (Option Name) :=
do some (ConstantInfo.inductInfo { ctors := ctor::_, ..}) ← getConst d | pure none;
   pure (some ctor)

private def mkNullaryCtor {m : Type → Type} [Monad m]
   (getConst : Name → m (Option ConstantInfo))
   (type : Expr) (nparams : Nat) : m (Option Expr) :=
match type.getAppFn with
| Expr.const d lvls => do
  (some ctor) ← getFirstCtor getConst d | pure none;
  pure $ mkApp (Expr.const ctor lvls) (type.getAppArgs.shrink nparams)
| _ => pure none

private def toCtorIfLit : Expr → Expr
| Expr.lit (Literal.natVal v) =>
  if v == 0 then Expr.const `Nat.zero []
  else Expr.app (Expr.const `Nat.succ []) (Expr.lit (Literal.natVal (v-1)))
| e => e

private def getRecRuleFor (rec : RecursorVal) (major : Expr) : Option RecursorRule :=
match major.getAppFn with
| Expr.const fn _ => rec.rules.find $ fun r => r.ctor == fn
| _ => none

@[specialize] private def toCtorWhenK {m : Type → Type} [Monad m]
    (getConst  : Name → m (Option ConstantInfo))
    (whnf      : Expr → m Expr)
    (inferType : Expr → m Expr)
    (isDefEq   : Expr → Expr → m Bool)
    (rec : RecursorVal) (major : Expr) : m (Option Expr) :=
do majorType ← inferType major;
   majorType ← whnf majorType;
   let majorTypeI := majorType.getAppFn;
   if !majorTypeI.isConstOf rec.getInduct then
     pure none
   else if majorType.hasExprMVar && majorType.getAppArgs.anyFrom Expr.hasExprMVar rec.nparams then
     pure none
   else do
     (some newCtorApp) ← mkNullaryCtor getConst majorType rec.nparams | pure none;
     newType ← inferType newCtorApp;
     defeq ← isDefEq majorType newType;
     pure $ if defeq then newCtorApp else none

/-- Auxiliary function for reducing recursor applications. -/
@[specialize] def reduceRec {α} {m : Type → Type} [Monad m]
    (getConst  : Name → m (Option ConstantInfo))
    (whnf      : Expr → m Expr)
    (inferType : Expr → m Expr)
    (isDefEq   : Expr → Expr → m Bool)
    (rec : RecursorVal) (recLvls : List Level) (recArgs : Array Expr)
    (failK : Unit → m α) (successK : Expr → m α) : m α :=
let majorIdx := rec.getMajorIdx;
if h : majorIdx < recArgs.size then do
  let major := recArgs.get ⟨majorIdx, h⟩;
  major ← whnf major;
  major ←
    if !rec.k then
      pure major
    else do {
      newMajor ← toCtorWhenK getConst whnf inferType isDefEq rec major;
      pure (newMajor.getD major)
    };
  let major := toCtorIfLit major;
  match getRecRuleFor rec major with
  | some rule =>
    let majorArgs := major.getAppArgs;
    if recLvls.length != rec.lparams.length then
      failK ()
    else
      let rhs := rule.rhs.instantiateLevelParams rec.lparams recLvls;
      -- Apply parameters, motives and minor premises from recursor application.
      let rhs := mkAppRange rhs 0 (rec.nparams+rec.nmotives+rec.nminors) recArgs;
      /- The number of parameters in the constructor is not necessarily
         equal to the number of parameters in the recursor when we have
         nested inductive types. -/
      let nparams := majorArgs.size - rule.nfields;
      let rhs := mkAppRange rhs nparams majorArgs.size majorArgs;
      let rhs := mkAppRange rhs (majorIdx + 1) recArgs.size recArgs;
      successK rhs
  | none => failK ()
else
  failK ()

@[specialize] def isRecStuck {m : Type → Type} [Monad m]
    (whnf    : Expr → m Expr)
    (isStuck : Expr → m (Option Expr))
    (rec : RecursorVal) (recLvls : List Level) (recArgs : Array Expr) : m (Option Expr) :=
if rec.k then
  -- TODO: improve this case
  pure none
else do
  let majorIdx := rec.getMajorIdx;
  if h : majorIdx < recArgs.size then do
    let major := recArgs.get ⟨majorIdx, h⟩;
    major ← whnf major;
    isStuck major
  else
    pure none

/- ===========================
   Helper functions for reducing Quot.lift and Quot.ind
   =========================== -/

/-- Auxiliary function for reducing `Quot.lift` and `Quot.ind` applications. -/
@[specialize] def reduceQuotRec {α} {m : Type → Type} [Monad m]
    (getConst : Name → m (Option ConstantInfo))
    (whnf     : Expr → m Expr)
    (rec  : QuotVal) (recLvls : List Level) (recArgs : Array Expr)
    (failK : Unit → m α) (successK : Expr → m α) : m α :=
let process (majorPos argPos : Nat) : m α :=
  if h : majorPos < recArgs.size then do
    let major := recArgs.get ⟨majorPos, h⟩;
    major ← whnf major;
    match major with
    | Expr.app (Expr.app (Expr.app (Expr.const majorFn _) _) _) majorArg => do
      some (ConstantInfo.quotInfo { kind := QuotKind.ctor, .. }) ← getConst majorFn | failK ();
      let f := recArgs.get! argPos;
      let r := Expr.app f majorArg;
      let recArity := majorPos + 1;
      successK $ mkAppRange r recArity recArgs.size recArgs
    | _ => failK ()
  else
    failK ();
match rec.kind with
| QuotKind.lift => process 5 3
| QuotKind.ind  => process 4 3
| _             => failK ()

@[specialize] def isQuotRecStuck {m : Type → Type} [Monad m]
    (whnf : Expr → m Expr)
    (isStuck : Expr → m (Option Expr))
    (rec : QuotVal) (recLvls : List Level) (recArgs : Array Expr) : m (Option Expr) :=
let process (majorPos : Nat) : m (Option Expr) :=
  if h : majorPos < recArgs.size then do
    let major := recArgs.get ⟨majorPos, h⟩;
    major ← whnf major;
    isStuck major
  else
    pure none;
match rec.kind with
| QuotKind.lift => process 5
| QuotKind.ind  => process 4
| _             => pure none

/- ===========================
   Helper function for extracting "stuck term"
   =========================== -/

/-- Return `some (Expr.mvar mvarId)` if metavariable `mvarId` is blocking reduction. -/
@[specialize] partial def getStuckMVar {m : Type → Type} [Monad m]
    (getConst : Name → m (Option ConstantInfo))
    (whnf     : Expr → m Expr)
    : Expr → m (Option Expr)
| Expr.mdata _ e   => getStuckMVar e
| Expr.proj _ _ e  => do e ← whnf e; getStuckMVar e
| e@(Expr.mvar _)  => pure (some e)
| e@(Expr.app f _) =>
  let f := f.getAppFn;
  match f with
  | Expr.mvar _            => pure (some f)
  | Expr.const fName fLvls => do
    cinfo? ← getConst fName;
    match cinfo? with
    | some $ ConstantInfo.recInfo rec  => isRecStuck whnf getStuckMVar rec fLvls e.getAppArgs
    | some $ ConstantInfo.quotInfo rec => isQuotRecStuck whnf getStuckMVar rec fLvls e.getAppArgs
    | _                                => pure none
  | _ => pure none
| _ => pure none

/- ===========================
   Weak Head Normal Form auxiliary combinators
   =========================== -/

/-- Auxiliary combinator for handling easy WHNF cases. It takes a function for handling the "hard" cases as an argument -/
@[specialize] partial def whnfEasyCases {m : Type → Type} [Monad m]
    (getLocalDecl      : Name → m LocalDecl)
    (getMVarAssignment : Name → m (Option Expr))
    : Expr → (Expr → m Expr) → m Expr
| e@(Expr.forallE _ _ _ _), _ => pure e
| e@(Expr.lam _ _ _ _),     _ => pure e
| e@(Expr.sort _),          _ => pure e
| e@(Expr.lit _),           _ => pure e
| e@(Expr.bvar _),          _ => unreachable!
| Expr.mdata _ e,           k => whnfEasyCases e k
| e@(Expr.letE _ _ _ _),    k => k e
| e@(Expr.fvar fvarId),     k => do
  decl ← getLocalDecl fvarId;
  match decl.valueOpt with
  | none   => pure e
  | some v => whnfEasyCases v k
| e@(Expr.mvar mvarId),     k => do
  v? ← getMVarAssignment mvarId;
  match v? with
  | some v => whnfEasyCases v k
  | none   => pure e
| e@(Expr.const _ _),       k => k e
| e@(Expr.app _ _),         k => k e
| e@(Expr.proj _ _ _),      k => k e

/-- Return true iff term is of the form `idRhs ...` -/
private def isIdRhsApp (e : Expr) : Bool :=
e.isAppOf `idRhs

/-- (@idRhs T f a_1 ... a_n) ==> (f a_1 ... a_n) -/
private def extractIdRhs (e : Expr) : Expr :=
if !isIdRhsApp e then e
else
  let args := e.getAppArgs;
  if args.size < 2 then e
  else mkAppRange (args.get! 1) 2 args.size args

@[specialize] private def deltaDefinition {α} (c : ConstantInfo) (lvls : List Level)
    (failK : Unit → α) (successK : Expr → α) : α :=
if c.lparams.length != lvls.length then failK ()
else
  let val := c.instantiateValueLevelParams lvls;
  successK (extractIdRhs val)

@[specialize] private def deltaBetaDefinition {α} (c : ConstantInfo) (lvls : List Level) (revArgs : Array Expr)
    (failK : Unit → α) (successK : Expr → α) : α :=
if c.lparams.length != lvls.length then failK ()
else
  let val := c.instantiateValueLevelParams lvls;
  let val := val.betaRev revArgs;
  successK (extractIdRhs val)

/--
  Apply beta-reduction, zeta-reduction (i.e., unfold let local-decls), iota-reduction,
  expand let-expressions, expand assigned meta-variables.

  This method does *not* apply delta-reduction at the head symbol `f` unless `isAuxDef? f` returns true.
  Reason: we want to perform these reductions lazily at `isDefEq`. -/
@[specialize] partial def whnfCore {m : Type → Type} [Monad m]
    (getConst          : Name → m (Option ConstantInfo))
    (isAuxDef?         : Name → m Bool)
    (whnf              : Expr → m Expr)
    (inferType         : Expr → m Expr)
    (isDefEq           : Expr → Expr → m Bool)
    (getLocalDecl      : Name → m LocalDecl)
    (getMVarAssignment : Name → m (Option Expr)) : Expr → m Expr
| e => whnfEasyCases getLocalDecl getMVarAssignment e $ fun e =>
  match e with
  | e@(Expr.const _ _)    => pure e
  | e@(Expr.letE _ _ v b) => whnfCore $ b.instantiate1 v
  | e@(Expr.app f _)      => do
    let f := f.getAppFn;
    f' ← whnfCore f;
    if f'.isLambda then
      let revArgs := e.getAppRevArgs;
      whnfCore $ f.betaRev revArgs
    else do
      let done : Unit → m Expr := fun _ =>
        if f == f' then pure e else pure $ e.updateFn f';
      matchConstAux getConst f' done $ fun cinfo lvls =>
        match cinfo with
        | ConstantInfo.recInfo rec    => reduceRec getConst whnf inferType isDefEq rec lvls e.getAppArgs done whnfCore
        | ConstantInfo.quotInfo rec   => reduceQuotRec getConst whnf rec lvls e.getAppArgs done whnfCore
        | c@(ConstantInfo.defnInfo _) => do
          unfold? ← isAuxDef? c.name;
          if unfold? then
            deltaBetaDefinition c lvls e.getAppArgs done whnfCore
          else
            done ()
        | _ => done ()
  | e@(Expr.proj _ i c) => do
    c   ← whnf c;
    matchConstAux getConst c.getAppFn (fun _ => pure e) $ fun cinfo lvls =>
      match cinfo with
      | ConstantInfo.ctorInfo ctorVal => pure $ c.getArgD (ctorVal.nparams + i) e
      | _ => pure e
  | _ => unreachable!

/--
  Similar to `whnfCore`, but uses `synthesizePending` to (try to) synthesize metavariables
  that are blocking reduction. -/
@[specialize] private partial def whnfCoreUnstuck {m : Type → Type} [Monad m]
    (getConst          : Name → m (Option ConstantInfo))
    (isAuxDef?         : Name → m Bool)
    (whnf              : Expr → m Expr)
    (inferType         : Expr → m Expr)
    (isDefEq           : Expr → Expr → m Bool)
    (synthesizePending : Expr → m Bool)
    (getLocalDecl      : Name → m LocalDecl)
    (getMVarAssignment : Name → m (Option Expr))
    : Expr → m Expr
| e => do
  e ← whnfCore getConst isAuxDef? whnf inferType isDefEq getLocalDecl getMVarAssignment e;
  (some mvar) ← getStuckMVar getConst whnf e | pure e;
  succeeded   ← synthesizePending mvar;
  if succeeded then whnfCoreUnstuck e else pure e

/-- Unfold definition using "smart unfolding" if possible. -/
@[specialize] def unfoldDefinition {α} {m : Type → Type} [Monad m]
    (getConst          : Name → m (Option ConstantInfo))
    (isAuxDef?         : Name → m Bool)
    (whnf              : Expr → m Expr)
    (inferType         : Expr → m Expr)
    (isDefEq           : Expr → Expr → m Bool)
    (synthesizePending : Expr → m Bool)
    (getLocalDecl      : Name → m LocalDecl)
    (getMVarAssignment : Name → m (Option Expr))
    (e : Expr)
    (failK : Unit → m α) (successK : Expr → m α) : m α :=
match e with
| Expr.app f _ =>
  matchConstAux getConst f.getAppFn failK $ fun fInfo fLvls =>
    if fInfo.lparams.length != fLvls.length then failK ()
    else do
      fAuxInfo? ← getConst (mkSmartUnfoldingNameFor fInfo.name);
      match fAuxInfo? with
      | some $ fAuxInfo@(ConstantInfo.defnInfo _) =>
        deltaBetaDefinition fAuxInfo fLvls e.getAppRevArgs failK $ fun e₁ => do
          e₂ ← whnfCoreUnstuck getConst isAuxDef? whnf inferType isDefEq synthesizePending getLocalDecl getMVarAssignment e₁;
          if isIdRhsApp e₂ then
            successK $ extractIdRhs e₂
          else
            failK ()
      | _ => deltaBetaDefinition fInfo fLvls e.getAppRevArgs failK successK
| Expr.const name lvls => do
  (some (cinfo@(ConstantInfo.defnInfo _))) ← getConst name | failK ();
  deltaDefinition cinfo lvls failK successK
| _ => failK ()

/- Reference implementation for `whnf`. It does not cache any results.

   How to use:
   - `getConst constName` retrieves `constName` from environment. Caller may make definitions opaque by returning `none`.
   - `isAuxDef? constName` returns `true` is `constName` is an auxiliary declaration automatically generated by Lean and
     used by equation compiler, and must be eagerly reduced by `whnfCore`. This method is usually implemented using `isAuxRecursor`.
   - `synthesizePending` is used to (try to) synthesize synthetic metavariables that may be blocking reduction.

   The other parameters should be self explanatory.  -/
@[specialize] partial def whnfMain {m : Type → Type} [Monad m]
    (getConst          : Name → m (Option ConstantInfo))
    (isAuxDef?         : Name → m Bool)
    (inferType         : Expr → m Expr)
    (isDefEq           : Expr → Expr → m Bool)
    (synthesizePending : Expr → m Bool)
    (getLocalDecl      : Name → m LocalDecl)
    (getMVarAssignment : Name → m (Option Expr))
    : Expr → m Expr
| e => do
  e ← whnfCore getConst isAuxDef? whnfMain inferType isDefEq getLocalDecl getMVarAssignment e;
  unfoldDefinition getConst isAuxDef? whnfMain inferType isDefEq synthesizePending getLocalDecl getMVarAssignment e (fun _ => pure e) whnfMain

end Lean
