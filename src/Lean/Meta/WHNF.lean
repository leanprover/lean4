/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Structure
import Lean.Util.Recognizers
import Lean.Meta.GetUnfoldableConst
import Lean.Meta.FunInfo
import Lean.Meta.Match.MatcherInfo
import Lean.Meta.Match.MatchPatternAttr

namespace Lean.Meta

-- ===========================
/-! # Smart unfolding support -/
-- ===========================

/--
Forward declaration. It is defined in the module `src/Lean/Elab/PreDefinition/Structural/Eqns.lean`.
It is possible to avoid this hack if we move `Structural.EqnInfo` and `Structural.eqnInfoExt`
to this module.
-/
@[extern "lean_get_structural_rec_arg_pos"]
opaque getStructuralRecArgPos? (declName : Name) : CoreM (Option Nat)

def smartUnfoldingSuffix := "_sunfold"

@[inline] def mkSmartUnfoldingNameFor (declName : Name) : Name :=
  Name.mkStr declName smartUnfoldingSuffix

def hasSmartUnfoldingDecl (env : Environment) (declName : Name) : Bool :=
  env.contains (mkSmartUnfoldingNameFor declName)

register_builtin_option smartUnfolding : Bool := {
  defValue := true
  descr := "when computing weak head normal form, use auxiliary definition created for functions defined by structural recursion"
}

/-- Add auxiliary annotation to indicate the `match`-expression `e` must be reduced when performing smart unfolding. -/
def markSmartUnfoldingMatch (e : Expr) : Expr :=
  mkAnnotation `sunfoldMatch e

def smartUnfoldingMatch? (e : Expr) : Option Expr :=
  annotation? `sunfoldMatch e

/-- Add auxiliary annotation to indicate expression `e` (a `match` alternative rhs) was successfully reduced by smart unfolding. -/
def markSmartUnfoldingMatchAlt (e : Expr) : Expr :=
  mkAnnotation `sunfoldMatchAlt e

def smartUnfoldingMatchAlt? (e : Expr) : Option Expr :=
  annotation? `sunfoldMatchAlt e

-- ===========================
/-! # Helper methods -/
-- ===========================

def isAuxDef (constName : Name) : MetaM Bool := do
  let env ← getEnv
  return isAuxRecursor env constName || isNoConfusion env constName

@[inline] private def matchConstAux {α} (e : Expr) (failK : Unit → MetaM α) (k : ConstantInfo → List Level → MetaM α) : MetaM α := do
  let .const name lvls := e
    | failK ()
  let (some cinfo) ← getUnfoldableConst? name
    | failK ()
  k cinfo lvls

-- ===========================
/-! # Helper functions for reducing recursors -/
-- ===========================

private def getFirstCtor (d : Name) : MetaM (Option Name) := do
  let some (ConstantInfo.inductInfo { ctors := ctor::_, ..}) ← getUnfoldableConstNoEx? d |
    return none
  return some ctor

private def mkNullaryCtor (type : Expr) (nparams : Nat) : MetaM (Option Expr) := do
  let .const d lvls := type.getAppFn
    | return none
  let (some ctor) ← getFirstCtor d | pure none
  return mkAppN (mkConst ctor lvls) (type.getAppArgs.shrink nparams)

private def getRecRuleFor (recVal : RecursorVal) (major : Expr) : Option RecursorRule :=
  match major.getAppFn with
  | .const fn _ => recVal.rules.find? fun r => r.ctor == fn
  | _           => none

private def toCtorWhenK (recVal : RecursorVal) (major : Expr) : MetaM Expr := do
  let majorType ← inferType major
  let majorType ← instantiateMVars (← whnf majorType)
  let majorTypeI := majorType.getAppFn
  if !majorTypeI.isConstOf recVal.getInduct then
    return major
  else if majorType.hasExprMVar && majorType.getAppArgs[recVal.numParams:].any Expr.hasExprMVar then
    return major
  else do
    let (some newCtorApp) ← mkNullaryCtor majorType recVal.numParams | pure major
    let newType ← inferType newCtorApp
    /- TODO: check whether changing reducibility to default hurts performance here.
       We do that to make sure auxiliary `Eq.rec` introduced by the `match`-compiler
       are reduced even when `TransparencyMode.reducible` (like in `simp`).

       We use `withNewMCtxDepth` to make sure metavariables at `majorType` are not assigned.
       For example, given `major : Eq ?x y`, we don't want to apply K by assigning `?x := y`.
    -/
    if (← withAtLeastTransparency TransparencyMode.default <| withNewMCtxDepth <| isDefEq majorType newType) then
      return newCtorApp
    else
      return major

/--
  Create the `i`th projection `major`. It tries to use the auto-generated projection functions if available. Otherwise falls back
  to `Expr.proj`.
-/
def mkProjFn (ctorVal : ConstructorVal) (us : List Level) (params : Array Expr) (i : Nat) (major : Expr) : CoreM Expr := do
  match getStructureInfo? (← getEnv) ctorVal.induct with
  | none => return mkProj ctorVal.induct i major
  | some info => match info.getProjFn? i with
    | none => return mkProj ctorVal.induct i major
    | some projFn => return mkApp (mkAppN (mkConst projFn us) params) major

/--
  If `major` is not a constructor application, and its type is a structure `C ...`, then return `C.mk major.1 ... major.n`

  \pre `inductName` is `C`.

  If `Meta.Config.etaStruct` is `false` or the condition above does not hold, this method just returns `major`. -/
private def toCtorWhenStructure (inductName : Name) (major : Expr) : MetaM Expr := do
  unless (← useEtaStruct inductName) do
    return major
  let env ← getEnv
  if !isStructureLike env inductName then
    return major
  else if let some _ := major.isConstructorApp? env then
    return major
  else
    let majorType ← inferType major
    let majorType ← instantiateMVars (← whnf majorType)
    let majorTypeI := majorType.getAppFn
    if !majorTypeI.isConstOf inductName then
      return major
    match majorType.getAppFn with
    | Expr.const d us =>
      if (← whnfD (← inferType majorType)) == mkSort levelZero then
        return major -- We do not perform eta for propositions, see implementation in the kernel
      else
        let some ctorName ← getFirstCtor d | pure major
        let ctorInfo ← getConstInfoCtor ctorName
        let params := majorType.getAppArgs.shrink ctorInfo.numParams
        let mut result := mkAppN (mkConst ctorName us) params
        for i in [:ctorInfo.numFields] do
          result := mkApp result (← mkProjFn ctorInfo us params i major)
        return result
    | _ => return major


-- Helper predicate that returns `true` for inductive predicates used to define functions by well-founded recursion.
private def isWFRec (declName : Name) : Bool :=
  declName == ``Acc.rec || declName == ``WellFounded.rec

/-- Auxiliary function for reducing recursor applications. -/
private def reduceRec (recVal : RecursorVal) (recLvls : List Level) (recArgs : Array Expr) (failK : Unit → MetaM α) (successK : Expr → MetaM α) : MetaM α :=
  let majorIdx := recVal.getMajorIdx
  if h : majorIdx < recArgs.size then do
    let major := recArgs.get ⟨majorIdx, h⟩
    let mut major ← if isWFRec recVal.name && (← getTransparency) == .default then
      -- If recursor is `Acc.rec` or `WellFounded.rec` and transparency is default,
      -- then we bump transparency to .all to make sure we can unfold defs defined by WellFounded recursion.
      -- We use this trick because we abstract nested proofs occurring in definitions.
      -- Alternative design: do not abstract nested proofs used to justify well-founded recursion.
      withTransparency .all <| whnf major
    else
      whnf major
    if recVal.k then
      major ← toCtorWhenK recVal major
    major := major.toCtorIfLit
    major ← toCtorWhenStructure recVal.getInduct major
    match getRecRuleFor recVal major with
    | some rule =>
      let majorArgs := major.getAppArgs
      if recLvls.length != recVal.levelParams.length then
        failK ()
      else
        let rhs := rule.rhs.instantiateLevelParams recVal.levelParams recLvls
        -- Apply parameters, motives and minor premises from recursor application.
        let rhs := mkAppRange rhs 0 (recVal.numParams+recVal.numMotives+recVal.numMinors) recArgs
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

-- ===========================
/-! # Helper functions for reducing Quot.lift and Quot.ind -/
-- ===========================

/-- Auxiliary function for reducing `Quot.lift` and `Quot.ind` applications. -/
private def reduceQuotRec (recVal  : QuotVal) (recLvls : List Level) (recArgs : Array Expr) (failK : Unit → MetaM α) (successK : Expr → MetaM α) : MetaM α :=
  let process (majorPos argPos : Nat) : MetaM α :=
    if h : majorPos < recArgs.size then do
      let major := recArgs.get ⟨majorPos, h⟩
      let major ← whnf major
      match major with
      | Expr.app (Expr.app (Expr.app (Expr.const majorFn _) _) _) majorArg => do
        let some (ConstantInfo.quotInfo { kind := QuotKind.ctor, .. }) ← getUnfoldableConstNoEx? majorFn | failK ()
        let f := recArgs[argPos]!
        let r := mkApp f majorArg
        let recArity := majorPos + 1
        successK <| mkAppRange r recArity recArgs.size recArgs
      | _ => failK ()
    else
      failK ()
  match recVal.kind with
  | QuotKind.lift => process 5 3
  | QuotKind.ind  => process 4 3
  | _             => failK ()

-- ===========================
/-! # Helper function for extracting "stuck term" -/
-- ===========================

mutual
  private partial def isRecStuck? (recVal : RecursorVal) (recArgs : Array Expr) : MetaM (Option MVarId) :=
    if recVal.k then
      -- TODO: improve this case
      return none
    else do
      let majorIdx := recVal.getMajorIdx
      if h : majorIdx < recArgs.size then do
        let major := recArgs.get ⟨majorIdx, h⟩
        let major ← whnf major
        getStuckMVar? major
      else
        return none

  private partial def isQuotRecStuck? (recVal : QuotVal) (recArgs : Array Expr) : MetaM (Option MVarId) :=
    let process? (majorPos : Nat) : MetaM (Option MVarId) :=
      if h : majorPos < recArgs.size then do
        let major := recArgs.get ⟨majorPos, h⟩
        let major ← whnf major
        getStuckMVar? major
      else
        return none
    match recVal.kind with
    | QuotKind.lift => process? 5
    | QuotKind.ind  => process? 4
    | _             => return none

  /-- Return `some (Expr.mvar mvarId)` if metavariable `mvarId` is blocking reduction. -/
  partial def getStuckMVar? (e : Expr) : MetaM (Option MVarId) := do
    match e with
    | .mdata _ e  => getStuckMVar? e
    | .proj _ _ e => getStuckMVar? (← whnf e)
    | .mvar .. =>
      let e ← instantiateMVars e
      match e with
      | .mvar mvarId => return some mvarId
      | _ => getStuckMVar? e
    | .app f .. =>
      let f := f.getAppFn
      match f with
      | .mvar .. =>
        let e ← instantiateMVars e
        match e.getAppFn with
        | .mvar mvarId => return some mvarId
        | _ => getStuckMVar? e
      | .const fName _ =>
        match (← getUnfoldableConstNoEx? fName) with
        | some <| .recInfo recVal  => isRecStuck? recVal e.getAppArgs
        | some <| .quotInfo recVal => isQuotRecStuck? recVal e.getAppArgs
        | _  =>
          unless e.hasExprMVar do return none
          -- Projection function support
          let some projInfo ← getProjectionFnInfo? fName | return none
          -- This branch is relevant if `e` is a type class projection that is stuck because the instance has not been synthesized yet.
          unless projInfo.fromClass do return none
          let args := e.getAppArgs
          -- First check whether `e`s instance is stuck.
          if let some major := args.get? projInfo.numParams then
            if let some mvarId ← getStuckMVar? major then
              return mvarId
          /-
          Then, recurse on the explicit arguments
          We want to detect the stuck instance in terms such as
          `HAdd.hAdd Nat Nat Nat (instHAdd Nat instAddNat) n (OfNat.ofNat Nat 2 ?m)`
          See issue https://github.com/leanprover/lean4/issues/1408 for an example where this is needed.
          -/
          let info ← getFunInfo f
          for pinfo in info.paramInfo, arg in args do
            if pinfo.isExplicit then
              if let some mvarId ← getStuckMVar? arg then
                return some mvarId
          return none
      | .proj _ _ e => getStuckMVar? (← whnf e)
      | _ => return none
    | _ => return none
end

-- ===========================
/-! # Weak Head Normal Form auxiliary combinators -/
-- ===========================

/--
Configuration for projection reduction. See `whnfCore`.
-/
inductive ProjReductionKind where
  /-- Projections `s.i` are not reduced at `whnfCore`. -/
  | no
  /--
  Projections `s.i` are reduced at `whnfCore`, and `whnfCore` is used at `s` during the process.
  Recall that `whnfCore` does not perform `delta` reduction (i.e., it will not unfold constant declarations).
  -/
  | yes
  /--
  Projections `s.i` are reduced at `whnfCore`, and `whnf` is used at `s` during the process.
  Recall that `whnfCore` does not perform `delta` reduction (i.e., it will not unfold constant declarations), but `whnf` does.
  -/
  | yesWithDelta
  deriving DecidableEq, Inhabited, Repr

/--
Configuration options for `whnfEasyCases` and `whnfCore`.
-/
structure WhnfCoreConfig where
  /-- If `true`, reduce recursor/matcher applications, e.g., `Nat.rec true (fun _ _ => false) Nat.zero` reduces to `true` -/
  iota : Bool := true
  /-- If `true`, reduce terms such as `(fun x => t[x]) a` into `t[a]` -/
  beta : Bool := true
  /-- Control projection reduction at `whnfCore`. -/
  proj : ProjReductionKind := .yesWithDelta
  /--
  Zeta reduction.
  It includes two kinds of reduction:
  - `let x := v; e[x]` reduces to `e[v]`.
  - Given a local context containing entry `x : t := e`, free variable `x` reduces to `e`.

  We say a let-declaration `let x := v; e` is non dependent if it is equivalent to `(fun x => e) v`.
  Recall that
  ```
  fun x : BitVec 5 => let n := 5; fun y : BitVec n => x = y
  ```
  is type correct, but
  ```
  fun x : BitVec 5 => (fun n => fun y : BitVec n => x = y) 5
  ```
  is not.
  -/
  zeta : Bool := true

/-- Auxiliary combinator for handling easy WHNF cases. It takes a function for handling the "hard" cases as an argument -/
@[specialize] partial def whnfEasyCases (e : Expr) (k : Expr → MetaM Expr) (config : WhnfCoreConfig := {}) : MetaM Expr := do
  match e with
  | .forallE ..    => return e
  | .lam ..        => return e
  | .sort ..       => return e
  | .lit ..        => return e
  | .bvar ..       => panic! "loose bvar in expression"
  | .letE ..       => k e
  | .const ..      => k e
  | .app ..        => k e
  | .proj ..       => k e
  | .mdata _ e     => whnfEasyCases e k config
  | .fvar fvarId   =>
    let decl ← fvarId.getDecl
    match decl with
    | .cdecl .. => return e
    | .ldecl (value := v) .. =>
      unless config.zeta do return e
      if (← getConfig).trackZeta then
        modify fun s => { s with zetaFVarIds := s.zetaFVarIds.insert fvarId }
      whnfEasyCases v k config
  | .mvar mvarId   =>
    match (← getExprMVarAssignment? mvarId) with
    | some v => whnfEasyCases v k config
    | none   => return e

@[specialize] private def deltaDefinition (c : ConstantInfo) (lvls : List Level)
    (failK : Unit → MetaM α) (successK : Expr → MetaM α) : MetaM α := do
  if c.levelParams.length != lvls.length then
    failK ()
  else
    successK (← instantiateValueLevelParams c lvls)

@[specialize] private def deltaBetaDefinition (c : ConstantInfo) (lvls : List Level) (revArgs : Array Expr)
    (failK : Unit → MetaM α) (successK : Expr → MetaM α) (preserveMData := false) : MetaM α := do
  if c.levelParams.length != lvls.length then
    failK ()
  else
    let val ← instantiateValueLevelParams c lvls
    let val := val.betaRev revArgs (preserveMData := preserveMData)
    successK val

inductive ReduceMatcherResult where
  | reduced (val : Expr)
  | stuck   (val : Expr)
  | notMatcher
  | partialApp

/--
  The "match" compiler uses `if-then-else` expressions and other auxiliary declarations to compile match-expressions such as
  ```
  match v with
  | 'a' => 1
  | 'b' => 2
  | _   => 3
  ```
  because it is more efficient than using `casesOn` recursors.
  The method `reduceMatcher?` fails if these auxiliary definitions (e.g., `ite`) cannot be unfolded in the current
  transparency setting. This is problematic because tactics such as `simp` use `TransparencyMode.reducible`, and
  most users assume that expressions such as
  ```
  match 0 with
  | 0 => 1
  | 100 => 2
  | _ => 3
  ```
  should reduce in any transparency mode.
  Thus, we define a custom `canUnfoldAtMatcher` predicate for `whnfMatcher`.

  This solution is not very modular because modifications at the `match` compiler require changes here.
  We claim this is defensible because it is reducing the auxiliary declaration defined by the `match` compiler.

  Alternative solution: tactics that use `TransparencyMode.reducible` should rely on the equations we generated for match-expressions.
  This solution is also not perfect because the match-expression above will not reduce during type checking when we are not using
  `TransparencyMode.default` or `TransparencyMode.all`.
-/
def canUnfoldAtMatcher (cfg : Config) (info : ConstantInfo) : CoreM Bool := do
  match cfg.transparency with
  | .all     => return true
  | .default => return !(← isIrreducible info.name)
  | _ =>
    if (← isReducible info.name) || isGlobalInstance (← getEnv) info.name then
      return true
    else if hasMatchPatternAttribute (← getEnv) info.name then
      return true
    else
      return info.name == ``ite
       || info.name == ``dite
       || info.name == ``decEq
       || info.name == ``Nat.decEq
       || info.name == ``Char.ofNat   || info.name == ``Char.ofNatAux
       || info.name == ``String.decEq || info.name == ``List.hasDecEq
       || info.name == ``Fin.ofNat
       || info.name == ``UInt8.ofNat  || info.name == ``UInt8.decEq
       || info.name == ``UInt16.ofNat || info.name == ``UInt16.decEq
       || info.name == ``UInt32.ofNat || info.name == ``UInt32.decEq
       || info.name == ``UInt64.ofNat || info.name == ``UInt64.decEq
       /- Remark: we need to unfold the following two definitions because they are used for `Fin`, and
          lazy unfolding at `isDefEq` does not unfold projections.  -/
       || info.name == ``HMod.hMod || info.name == ``Mod.mod

private def whnfMatcher (e : Expr) : MetaM Expr := do
  /- When reducing `match` expressions, if the reducibility setting is at `TransparencyMode.reducible`,
     we increase it to `TransparencyMode.instances`. We use the `TransparencyMode.reducible` in many places (e.g., `simp`),
     and this setting prevents us from reducing `match` expressions where the discriminants are terms such as `OfNat.ofNat α n inst`.
     For example, `simp [Int.div]` will not unfold the application `Int.div 2 1` occurring in the target.

     TODO: consider other solutions; investigate whether the solution above produces counterintuitive behavior.  -/
  if (← getTransparency) matches .instances | .reducible then
    -- Also unfold some default-reducible constants; see `canUnfoldAtMatcher`
    withTransparency .instances <| withReader (fun ctx => { ctx with canUnfold? := canUnfoldAtMatcher }) do
      whnf e
  else
    -- Do NOT use `canUnfoldAtMatcher` here as it does not affect all/default reducibility and inhibits caching (#2564).
    -- In the future, we want to work on better reduction strategies that do not require caching.
    whnf e

def reduceMatcher? (e : Expr) : MetaM ReduceMatcherResult := do
  let .const declName declLevels := e.getAppFn
    | return .notMatcher
  let some info ← getMatcherInfo? declName
    | return .notMatcher
  let args := e.getAppArgs
  let prefixSz := info.numParams + 1 + info.numDiscrs
  if args.size < prefixSz + info.numAlts then
    return ReduceMatcherResult.partialApp
  let constInfo ← getConstInfo declName
  let f ← instantiateValueLevelParams constInfo declLevels
  let auxApp := mkAppN f args[0:prefixSz]
  let auxAppType ← inferType auxApp
  forallBoundedTelescope auxAppType info.numAlts fun hs _ => do
    let auxApp ← whnfMatcher (mkAppN auxApp hs)
    let auxAppFn := auxApp.getAppFn
    let mut i := prefixSz
    for h in hs do
      if auxAppFn == h then
        let result := mkAppN args[i]! auxApp.getAppArgs
        let result := mkAppN result args[prefixSz + info.numAlts:args.size]
        return ReduceMatcherResult.reduced result.headBeta
      i := i + 1
    return ReduceMatcherResult.stuck auxApp

private def projectCore? (e : Expr) (i : Nat) : MetaM (Option Expr) := do
  let e := e.toCtorIfLit
  matchConstCtor e.getAppFn (fun _ => pure none) fun ctorVal _ =>
    let numArgs := e.getAppNumArgs
    let idx := ctorVal.numParams + i
    if idx < numArgs then
      return some (e.getArg! idx)
    else
      return none

def project? (e : Expr) (i : Nat) : MetaM (Option Expr) := do
  projectCore? (← whnf e) i

/-- Reduce kernel projection `Expr.proj ..` expression. -/
def reduceProj? (e : Expr) : MetaM (Option Expr) := do
  match e with
  | .proj _ i c => project? c i
  | _           => return none

/--
  Auxiliary method for reducing terms of the form `?m t_1 ... t_n` where `?m` is delayed assigned.
  Recall that we can only expand a delayed assignment when all holes/metavariables in the assigned value have been "filled".
-/
private def whnfDelayedAssigned? (f' : Expr) (e : Expr) : MetaM (Option Expr) := do
  if f'.isMVar then
    match (← getDelayedMVarAssignment? f'.mvarId!) with
    | none => return none
    | some { fvars, mvarIdPending } =>
      let args := e.getAppArgs
      if fvars.size > args.size then
        -- Insufficient number of argument to expand delayed assignment
        return none
      else
        let newVal ← instantiateMVars (mkMVar mvarIdPending)
        if newVal.hasExprMVar then
           -- Delayed assignment still contains metavariables
           return none
        else
           let newVal := newVal.abstract fvars
           let result := newVal.instantiateRevRange 0 fvars.size args
           return mkAppRange result fvars.size args.size args
  else
    return none

/--
Apply beta-reduction, zeta-reduction (i.e., unfold let local-decls), iota-reduction,
expand let-expressions, expand assigned meta-variables.

The parameter `deltaAtProj` controls how to reduce projections `s.i`. If `deltaAtProj == true`,
then delta reduction is used to reduce `s` (i.e., `whnf` is used), otherwise `whnfCore`.

If `simpleReduceOnly`, then `iota` and projection reduction are not performed.
Note that the value of `deltaAtProj` is irrelevant if `simpleReduceOnly = true`.
-/
partial def whnfCore (e : Expr) (config : WhnfCoreConfig := {}): MetaM Expr :=
  go e
where
  go (e : Expr) : MetaM Expr :=
    whnfEasyCases e (config := config) fun e => do
      trace[Meta.whnf] e
      match e with
      | .const ..  => pure e
      | .letE _ _ v b _ => if config.zeta then go <| b.instantiate1 v else return e
      | .app f ..       =>
        if config.zeta then
          if let some (args, _, _, v, b) := e.letFunAppArgs? then
            -- When zeta reducing enabled, always reduce `letFun` no matter the current reducibility level
            return (← go <| mkAppN (b.instantiate1 v) args)
        let f := f.getAppFn
        let f' ← go f
        if config.beta && f'.isLambda then
          let revArgs := e.getAppRevArgs
          go <| f'.betaRev revArgs
        else if let some eNew ← whnfDelayedAssigned? f' e then
          go eNew
        else
          let e := if f == f' then e else e.updateFn f'
          unless config.iota do return e
          match (← reduceMatcher? e) with
          | .reduced eNew => go eNew
          | .partialApp   => pure e
          | .stuck _      => pure e
          | .notMatcher   =>
            matchConstAux f' (fun _ => return e) fun cinfo lvls =>
              match cinfo with
              | .recInfo rec    => reduceRec rec lvls e.getAppArgs (fun _ => return e) go
              | .quotInfo rec   => reduceQuotRec rec lvls e.getAppArgs (fun _ => return e) go
              | c@(.defnInfo _) => do
                if (← isAuxDef c.name) then
                  deltaBetaDefinition c lvls e.getAppRevArgs (fun _ => return e) go
                else
                  return e
              | _ => return e
      | .proj _ i c =>
        if config.proj == .no then return e
        let c ← if config.proj == .yesWithDelta then whnf c else go c
        match (← projectCore? c i) with
        | some e => go e
        | none => return e
      | _ => unreachable!

/--
  Recall that `_sunfold` auxiliary definitions contains the markers: `markSmartUnfoldingMatch` (*) and `markSmartUnfoldingMatchAlt` (**).
  For example, consider the following definition
  ```
  def r (i j : Nat) : Nat :=
    i +
      match j with
      | Nat.zero => 1
      | Nat.succ j =>
        i + match j with
            | Nat.zero => 2
            | Nat.succ j => r i j
  ```
  produces the following `_sunfold` auxiliary definition with the markers
  ```
  def r._sunfold (i j : Nat) : Nat :=
    i +
      (*) match j with
      | Nat.zero => (**) 1
      | Nat.succ j =>
        i + (*) match j with
            | Nat.zero => (**) 2
            | Nat.succ j => (**) r i j
  ```

  `match` expressions marked with `markSmartUnfoldingMatch` (*) must be reduced, otherwise the resulting term is not definitionally
   equal to the given expression. The recursion may be interrupted as soon as the annotation `markSmartUnfoldingAlt` (**) is reached.

  For example, the term `r i j.succ.succ` reduces to the definitionally equal term `i + i * r i j`
-/
partial def smartUnfoldingReduce? (e : Expr) : MetaM (Option Expr) :=
  go e |>.run
where
  go (e : Expr) : OptionT MetaM Expr := do
    match e with
    | .letE n t v b _ => withLetDecl n t (← go v) fun x => do mkLetFVars #[x] (← go (b.instantiate1 x))
    | .lam .. => lambdaTelescope e fun xs b => do mkLambdaFVars xs (← go b)
    | .app f a .. => return mkApp (← go f) (← go a)
    | .proj _ _ s => return e.updateProj! (← go s)
    | .mdata _ b  =>
      if let some m := smartUnfoldingMatch? e then
        goMatch m
      else
        return e.updateMData! (← go b)
    | _ => return e

  goMatch (e : Expr) : OptionT MetaM Expr := do
    match (← reduceMatcher? e) with
    | ReduceMatcherResult.reduced e =>
      if let some alt := smartUnfoldingMatchAlt? e then
        return alt
      else
        go e
    | ReduceMatcherResult.stuck e' =>
      let mvarId ← getStuckMVar? e'
      /- Try to "unstuck" by resolving pending TC problems -/
      if (← Meta.synthPending mvarId) then
        goMatch e
      else
        failure
    | _ => failure

mutual

  /--
    Auxiliary method for unfolding a class projection.
  -/
  partial def unfoldProjInst? (e : Expr) : MetaM (Option Expr) := do
    match e.getAppFn with
    | .const declName .. =>
      match (← getProjectionFnInfo? declName) with
      | some { fromClass := true, .. } =>
        match (← withDefault <| unfoldDefinition? e) with
        | none   => return none
        | some e =>
          match (← withReducibleAndInstances <| reduceProj? e.getAppFn) with
          | none   => return none
          | some r => return mkAppN r e.getAppArgs |>.headBeta
      | _ => return none
    | _ => return none

  /--
    Auxiliary method for unfolding a class projection. when transparency is set to `TransparencyMode.instances`.
    Recall that class instance projections are not marked with `[reducible]` because we want them to be
    in "reducible canonical form".
  -/
  partial def unfoldProjInstWhenIntances? (e : Expr) : MetaM (Option Expr) := do
    if (← getTransparency) != TransparencyMode.instances then
      return none
    else
      unfoldProjInst? e

  /-- Unfold definition using "smart unfolding" if possible. -/
  partial def unfoldDefinition? (e : Expr) : MetaM (Option Expr) :=
    match e with
    | .app f _ =>
      matchConstAux f.getAppFn (fun _ => unfoldProjInstWhenIntances? e) fun fInfo fLvls => do
        if fInfo.levelParams.length != fLvls.length then
          return none
        else
          let unfoldDefault (_ : Unit) : MetaM (Option Expr) :=
            if fInfo.hasValue then
              deltaBetaDefinition fInfo fLvls e.getAppRevArgs (fun _ => pure none) (fun e => pure (some e))
            else
              return none
          if smartUnfolding.get (← getOptions) then
            match ((← getEnv).find? (mkSmartUnfoldingNameFor fInfo.name)) with
            | some fAuxInfo@(.defnInfo _) =>
              -- We use `preserveMData := true` to make sure the smart unfolding annotation are not erased in an over-application.
              deltaBetaDefinition fAuxInfo fLvls e.getAppRevArgs (preserveMData := true) (fun _ => pure none) fun e₁ => do
                let some r ← smartUnfoldingReduce? e₁ | return none
                /-
                  If `smartUnfoldingReduce?` succeeds, we should still check whether the argument the
                  structural recursion is recursing on reduces to a constructor.
                  This extra check is necessary in definitions (see issue #1081) such as
                  ```
                  inductive Vector (α : Type u) : Nat → Type u where
                    | nil  : Vector α 0
                    | cons : α → Vector α n → Vector α (n+1)

                  def Vector.insert (a: α) (i : Fin (n+1)) (xs : Vector α n) : Vector α (n+1) :=
                    match i, xs with
                    | ⟨0,   _⟩,        xs => cons a xs
                    | ⟨i+1, h⟩, cons x xs => cons x (xs.insert a ⟨i, Nat.lt_of_succ_lt_succ h⟩)
                  ```
                  The structural recursion is being performed using the vector `xs`. That is, we used `Vector.brecOn` to define
                  `Vector.insert`. Thus, an application `xs.insert a ⟨0, h⟩` is **not** definitionally equal to
                  `Vector.cons a xs` because `xs` is not a constructor application (the `Vector.brecOn` application is blocked).

                  Remark 1: performing structural recursion on `Fin (n+1)` is not an option here because it is a `Subtype` and
                  and the repacking in recursive applications confuses the structural recursion module.

                  Remark 2: the match expression reduces reduces to `cons a xs` when the discriminants are `⟨0, h⟩` and `xs`.

                  Remark 3: this check is unnecessary in most cases, but we don't need dependent elimination to trigger the issue                        fixed by this extra check. Here is another example that triggers the issue fixed by this check.
                  ```
                  def f : Nat → Nat → Nat
                    | 0,   y   => y
                    | x+1, y+1 => f (x-2) y
                    | x+1, 0   => 0

                  theorem ex : f 0 y = y := rfl
                  ```

                  Remark 4: the `return some r` in the following `let` is not a typo. Binport generated .olean files do not
                  store the position of recursive arguments for definitions using structural recursion.
                  Thus, we should keep `return some r` until Mathlib has been ported to Lean 3.
                  Note that the `Vector` example above does not even work in Lean 3.
                -/
                let some recArgPos ← getStructuralRecArgPos? fInfo.name | return some r
                let numArgs := e.getAppNumArgs
                if recArgPos >= numArgs then return none
                let recArg := e.getArg! recArgPos numArgs
                if !(← whnfMatcher recArg).isConstructorApp (← getEnv) then return none
                return some r
            | _ =>
              if (← getMatcherInfo? fInfo.name).isSome then
                -- Recall that `whnfCore` tries to reduce "matcher" applications.
                return none
              else
                unfoldDefault ()
          else
            unfoldDefault ()
    | .const declName lvls => do
      if smartUnfolding.get (← getOptions) && (← getEnv).contains (mkSmartUnfoldingNameFor declName) then
        return none
      else
        let some cinfo ← getUnfoldableConstNoEx? declName | pure none
        unless cinfo.hasValue do return none
        deltaDefinition cinfo lvls
          (fun _ => pure none)
          (fun e => pure (some e))
    | _ => return none
end

def unfoldDefinition (e : Expr) : MetaM Expr := do
  let some e ← unfoldDefinition? e | throwError "failed to unfold definition{indentExpr e}"
  return e

@[specialize] partial def whnfHeadPred (e : Expr) (pred : Expr → MetaM Bool) : MetaM Expr :=
  whnfEasyCases e fun e => do
    let e ← whnfCore e
    if (← pred e) then
        match (← unfoldDefinition? e) with
        | some e => whnfHeadPred e pred
        | none   => return e
    else
      return e

def whnfUntil (e : Expr) (declName : Name) : MetaM (Option Expr) := do
  let e ← whnfHeadPred e (fun e => return !e.isAppOf declName)
  if e.isAppOf declName then
    return e
  else
    return none

/-- Try to reduce matcher/recursor/quot applications. We say they are all "morally" recursor applications. -/
def reduceRecMatcher? (e : Expr) : MetaM (Option Expr) := do
  if !e.isApp then
    return none
  else match (← reduceMatcher? e) with
    | .reduced e => return e
    | _ => matchConstAux e.getAppFn (fun _ => pure none) fun cinfo lvls => do
      match cinfo with
      | .recInfo «rec»  => reduceRec «rec» lvls e.getAppArgs (fun _ => pure none) (fun e => pure (some e))
      | .quotInfo «rec» => reduceQuotRec «rec» lvls e.getAppArgs (fun _ => pure none) (fun e => pure (some e))
      | c@(.defnInfo _) =>
        if (← isAuxDef c.name) then
          deltaBetaDefinition c lvls e.getAppRevArgs (fun _ => pure none) (fun e => pure (some e))
        else
          return none
      | _ => return none

unsafe def reduceBoolNativeUnsafe (constName : Name) : MetaM Bool := evalConstCheck Bool `Bool constName
unsafe def reduceNatNativeUnsafe (constName : Name) : MetaM Nat := evalConstCheck Nat `Nat constName
@[implemented_by reduceBoolNativeUnsafe] opaque reduceBoolNative (constName : Name) : MetaM Bool
@[implemented_by reduceNatNativeUnsafe] opaque reduceNatNative (constName : Name) : MetaM Nat

def reduceNative? (e : Expr) : MetaM (Option Expr) :=
  match e with
  | Expr.app (Expr.const fName _) (Expr.const argName _) =>
    if fName == ``Lean.reduceBool then do
      return toExpr (← reduceBoolNative argName)
    else if fName == ``Lean.reduceNat then do
      return toExpr (← reduceNatNative argName)
    else
      return none
  | _ =>
    return none

@[inline] def withNatValue {α} (a : Expr) (k : Nat → MetaM (Option α)) : MetaM (Option α) := do
  let a ← whnf a
  match a with
  | Expr.const `Nat.zero _      => k 0
  | Expr.lit (Literal.natVal v) => k v
  | _                           => return none

def reduceUnaryNatOp (f : Nat → Nat) (a : Expr) : MetaM (Option Expr) :=
  withNatValue a fun a =>
  return mkRawNatLit <| f a

def reduceBinNatOp (f : Nat → Nat → Nat) (a b : Expr) : MetaM (Option Expr) :=
  withNatValue a fun a =>
  withNatValue b fun b => do
  trace[Meta.isDefEq.whnf.reduceBinOp] "{a} op {b}"
  return mkRawNatLit <| f a b

def reduceBinNatPred (f : Nat → Nat → Bool) (a b : Expr) : MetaM (Option Expr) := do
  withNatValue a fun a =>
  withNatValue b fun b =>
  return toExpr <| f a b

def reduceNat? (e : Expr) : MetaM (Option Expr) :=
  if e.hasFVar || e.hasMVar then
    return none
  else match e with
    | .app (.const fn _) a                =>
      if fn == ``Nat.succ then
        reduceUnaryNatOp Nat.succ a
      else
        return none
    | .app (.app (.const fn _) a1) a2 =>
      if fn == ``Nat.add then reduceBinNatOp Nat.add a1 a2
      else if fn == ``Nat.sub then reduceBinNatOp Nat.sub a1 a2
      else if fn == ``Nat.mul then reduceBinNatOp Nat.mul a1 a2
      else if fn == ``Nat.div then reduceBinNatOp Nat.div a1 a2
      else if fn == ``Nat.mod then reduceBinNatOp Nat.mod a1 a2
      else if fn == ``Nat.pow then reduceBinNatOp Nat.pow a1 a2
      else if fn == ``Nat.gcd then reduceBinNatOp Nat.gcd a1 a2
      else if fn == ``Nat.beq then reduceBinNatPred Nat.beq a1 a2
      else if fn == ``Nat.ble then reduceBinNatPred Nat.ble a1 a2
      else return none
    | _ =>
      return none


@[inline] private def useWHNFCache (e : Expr) : MetaM Bool := do
  -- We cache only closed terms without expr metavars.
  -- Potential refinement: cache if `e` is not stuck at a metavariable
  if e.hasFVar || e.hasExprMVar || (← read).canUnfold?.isSome then
    return false
  else
    match (← getConfig).transparency with
    | .default => return true
    | .all     => return true
    | _        => return false

@[inline] private def cached? (useCache : Bool) (e : Expr) : MetaM (Option Expr) := do
  if useCache then
    match (← getConfig).transparency with
    | .default => return (← get).cache.whnfDefault.find? e
    | .all     => return (← get).cache.whnfAll.find? e
    | _        => unreachable!
  else
    return none

private def cache (useCache : Bool) (e r : Expr) : MetaM Expr := do
  if useCache then
    match (← getConfig).transparency with
    | .default => modify fun s => { s with cache.whnfDefault := s.cache.whnfDefault.insert e r }
    | .all     => modify fun s => { s with cache.whnfAll     := s.cache.whnfAll.insert e r }
    | _        => unreachable!
  return r

@[export lean_whnf]
partial def whnfImp (e : Expr) : MetaM Expr :=
  withIncRecDepth <| whnfEasyCases e fun e => do
    checkSystem "whnf"
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
          | some e'' => cache useCache e (← whnfImp e'')
          | none => cache useCache e e'

/-- If `e` is a projection function that satisfies `p`, then reduce it -/
def reduceProjOf? (e : Expr) (p : Name → Bool) : MetaM (Option Expr) := do
  if !e.isApp then
    pure none
  else match e.getAppFn with
    | .const name .. => do
      let env ← getEnv
      match env.getProjectionStructureName? name with
      | some structName =>
        if p structName then
          Meta.unfoldDefinition? e
        else
          pure none
      | none => pure none
    | _ => pure none

builtin_initialize
  registerTraceClass `Meta.whnf
  registerTraceClass `Meta.isDefEq.whnf.reduceBinOp

end Lean.Meta
