/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Meta.AppBuilder
import Lean.Meta.CongrTheorems
import Lean.Meta.Eqns
import Lean.Meta.Tactic.Replace
import Lean.Meta.Tactic.Simp.SimpTheorems
import Lean.Meta.Tactic.Simp.SimpCongrTheorems

namespace Lean.Meta
namespace Simp

/-- The result of simplifying some expression `e`. -/
structure Result where
  /-- The simplified version of `e` -/
  expr           : Expr
  /-- A proof that `$e = $expr`, where the simplified expression is on the RHS.
  If `none`, the proof is assumed to be `refl`. -/
  proof?         : Option Expr := none
  /--
  If `cache := true` the result is cached.
  Warning: we will remove this field in the future. It is currently used by
  `arith := true`, but we can now refactor the code to avoid the hack.
  -/
  cache          : Bool := true
  deriving Inhabited

def mkEqTransOptProofResult (h? : Option Expr) (cache : Bool) (r : Result) : MetaM Result :=
  match h?, cache with
  | none, true  => return r
  | none, false => return { r with cache := false }
  | some p₁, cache => match r.proof? with
    | none    => return { r with proof? := some p₁, cache := cache && r.cache }
    | some p₂ => return { r with proof? := (← Meta.mkEqTrans p₁ p₂), cache := cache && r.cache }

def Result.mkEqTrans (r₁ r₂ : Result) : MetaM Result :=
  mkEqTransOptProofResult r₁.proof? r₁.cache r₂

/-- Flip the proof in a `Simp.Result`. -/
def Result.mkEqSymm (e : Expr) (r : Simp.Result) : MetaM Simp.Result :=
  match r.proof? with
  | none   => return { r with expr := e }
  | some p => return { r with expr := e, proof? := some (← Meta.mkEqSymm p) }

-- We use `SExprMap` because we want to discard cached results after a `discharge?`
abbrev Cache := SExprMap Result

abbrev CongrCache := ExprMap (Option CongrTheorem)

structure Context where
  private mk ::
  config            : Config := {}
  /-- Local declarations to propagate to `Meta.Context` -/
  zetaDeltaSet      : FVarIdSet := {}
  /--
  When processing `Simp` arguments, `zetaDelta` may be performed if `zetaDeltaSet` is not empty.
  We save the local free variable ids in `initUsedZetaDelta`. `initUsedZetaDelta` is a subset of `zetaDeltaSet`. -/
  initUsedZetaDelta : FVarIdSet := {}
  metaConfig        : ConfigWithKey := default
  indexConfig       : ConfigWithKey := default
  /-- `maxDischargeDepth` from `config` as an `UInt32`. -/
  maxDischargeDepth : UInt32 := UInt32.ofNatTruncate config.maxDischargeDepth
  simpTheorems      : SimpTheoremsArray := {}
  congrTheorems     : SimpCongrTheorems := {}
  /--
  Stores the "parent" term for the term being simplified.
  If a simplification procedure result depends on this value,
  then it is its reponsability to set `Result.cache := false`.

  Motivation for this field:
  Suppose we have a simplification procedure for normalizing arithmetic terms.
  Then, given a term such as `t_1 + ... + t_n`, we don't want to apply the procedure
  to every subterm `t_1 + ... + t_i` for `i < n` for performance issues. The procedure
  can accomplish this by checking whether the parent term is also an arithmetical expression
  and do nothing if it is. However, it should set `Result.cache := false` to ensure
  we don't miss simplification opportunities. For example, consider the following:
  ```
  example (x y : Nat) (h : y = 0) : id ((x + x) + y) = id (x + x) := by
    simp_arith only
    ...
  ```
  If we don't set `Result.cache := false` for the first `x + x`, then we get
  the resulting state:
  ```
  ... |- id (2*x + y) = id (x + x)
  ```
  instead of
  ```
  ... |- id (2*x + y) = id (2*x)
  ```
  as expected.

  Remark: given an application `f a b c` the "parent" term for `f`, `a`, `b`, and `c`
  is `f a b c`.
  -/
  parent?           : Option Expr := none
  dischargeDepth    : UInt32 := 0
  /--
  Number of indices in the local context when starting `simp`.
  We use this information to decide which assumptions we can use without
  invalidating the cache.
  -/
  lctxInitIndices   : Nat := 0
  /--
  If `inDSimp := true`, then `simp` is in `dsimp` mode, and only applying
  transformations that presereve definitional equality.
  -/
  inDSimp : Bool := false
  deriving Inhabited

/--
Helper method for bootstrapping purposes.
It disables `arith` if support theorems have not been defined yet.
-/
private def updateArith (c : Config) : CoreM Config := do
  if c.arith then
    if (← getEnv).contains ``Nat.Linear.ExprCnstr.eq_of_toNormPoly_eq then
      return c
    else
      return { c with arith := false }
  else
    return c

/--
Converts `Simp.Config` into `Meta.ConfigWithKey` used for indexing.
-/
private def mkIndexConfig (c : Config) : MetaM ConfigWithKey := do
  let curr ← Meta.getConfig
  return { curr with
    beta         := c.beta
    iota         := c.iota
    zeta         := c.zeta
    zetaUnused   := c.zetaUnused
    zetaDelta    := c.zetaDelta
    etaStruct    := c.etaStruct
    /-
    When indexing terms we disable projection to ensure a term such as `f ((a, b).1)`
    is an instance of the pattern `f (?x.1)`
    -/
    proj         := .no
    transparency := .reducible
  : Meta.Config }.toConfigWithKey

/--
Converts `Simp.Config` into `Meta.ConfigWithKey` used for `isDefEq`.
-/
private def mkMetaConfig (c : Config) : MetaM ConfigWithKey := do
  let curr ← Meta.getConfig
  return { curr with
    beta         := c.beta
    zeta         := c.zeta
    iota         := c.iota
    zetaUnused   := c.zetaUnused
    zetaDelta    := c.zetaDelta
    etaStruct    := c.etaStruct
    proj         := if c.proj then .yesWithDelta else .no
    transparency := .reducible
  : Meta.Config }.toConfigWithKey

def mkContext (config : Config := {}) (simpTheorems : SimpTheoremsArray := {}) (congrTheorems : SimpCongrTheorems := {}) : MetaM Context := do
  let config ← updateArith config
  return {
    config, simpTheorems, congrTheorems
    metaConfig := (← mkMetaConfig config)
    indexConfig := (← mkIndexConfig config)
  }

def Context.setConfig (context : Context) (config : Config) : MetaM Context := do
  return { context with
    config
    metaConfig := (← mkMetaConfig config)
    indexConfig := (← mkIndexConfig config)
  }

def Context.setSimpTheorems (c : Context) (simpTheorems : SimpTheoremsArray) : Context :=
  { c with simpTheorems }

def Context.setLctxInitIndices (c : Context) : MetaM Context :=
  return { c with lctxInitIndices := (← getLCtx).numIndices }

def Context.setAutoUnfold (c : Context) : Context :=
  { c with config.autoUnfold := true }

def Context.setFailIfUnchanged (c : Context) (flag : Bool) : Context :=
  { c with config.failIfUnchanged := flag }

def Context.setMemoize (c : Context) (flag : Bool) : Context :=
  { c with config.memoize := flag }

def Context.setZetaDeltaSet (c : Context) (zetaDeltaSet : FVarIdSet) (initUsedZetaDelta : FVarIdSet) : Context :=
  { c with zetaDeltaSet, initUsedZetaDelta }

def Context.isDeclToUnfold (ctx : Context) (declName : Name) : Bool :=
  ctx.simpTheorems.isDeclToUnfold declName

structure UsedSimps where
  -- We should use `PHashMap` because we backtrack the contents of `UsedSimps`
  -- The natural number tracks the insertion order
  map  : PHashMap Origin Nat := {}
  size : Nat := 0
  deriving Inhabited

def UsedSimps.insert (s : UsedSimps) (thmId : Origin) : UsedSimps :=
  if s.map.contains thmId then
    s
  else match s with
    | { map, size } => { map := map.insert thmId size, size := size + 1 }

def UsedSimps.toArray (s : UsedSimps) : Array Origin :=
  s.map.toArray.qsort (·.2 < ·.2) |>.map (·.1)

structure Diagnostics where
  /-- Number of times each simp theorem has been used/applied. -/
  usedThmCounter : PHashMap Origin Nat := {}
  /-- Number of times each simp theorem has been tried. -/
  triedThmCounter : PHashMap Origin Nat := {}
  /-- Number of times each congr theorem has been tried. -/
  congrThmCounter : PHashMap Name Nat := {}
  /--
  When using `Simp.Config.index := false`, and `set_option diagnostics true`,
  for every theorem used by `simp`, we check whether the theorem would be
  also applied if `index := true`, and we store it here if it would not have
  been tried.
  -/
  thmsWithBadKeys : PArray SimpTheorem := {}
  deriving Inhabited

structure State where
  cache        : Cache := {}
  congrCache   : CongrCache := {}
  usedTheorems : UsedSimps := {}
  numSteps     : Nat := 0
  diag         : Diagnostics := {}

structure Stats where
  usedTheorems : UsedSimps := {}
  diag : Diagnostics := {}
  deriving Inhabited

private opaque MethodsRefPointed : NonemptyType.{0}

private def MethodsRef : Type := MethodsRefPointed.type

instance : Nonempty MethodsRef := MethodsRefPointed.property

abbrev SimpM := ReaderT MethodsRef $ ReaderT Context $ StateRefT State MetaM

@[inline] def withIncDischargeDepth : SimpM α → SimpM α :=
  withTheReader Context (fun ctx => { ctx with dischargeDepth := ctx.dischargeDepth + 1 })

@[inline] def withSimpTheorems (s : SimpTheoremsArray) : SimpM α → SimpM α :=
  withTheReader Context (fun ctx => { ctx with simpTheorems := s })

@[inline] def withInDSimp : SimpM α → SimpM α :=
  withTheReader Context (fun ctx => { ctx with inDSimp := true })

/--
Executes `x` using a `MetaM` configuration for indexing terms.
It is inferred from `Simp.Config`.
For example, if the user has set `simp (config := { zeta := false })`,
`isDefEq` and `whnf` in `MetaM` should not perform `zeta` reduction.
-/
@[inline] def withSimpIndexConfig (x : SimpM α) : SimpM α := do
  withConfigWithKey (← readThe Simp.Context).indexConfig x

/--
Executes `x` using a `MetaM` configuration for inferred from `Simp.Config`.
-/
@[inline] def withSimpMetaConfig (x : SimpM α) : SimpM α := do
  withConfigWithKey (← readThe Simp.Context).metaConfig x

@[extern "lean_simp"]
opaque simp (e : Expr) : SimpM Result

@[extern "lean_dsimp"]
opaque dsimp (e : Expr) : SimpM Expr

@[inline] def modifyDiag (f : Diagnostics → Diagnostics) : SimpM Unit := do
  if (← isDiagnosticsEnabled) then
    modify fun { cache, congrCache, usedTheorems, numSteps, diag } => { cache, congrCache, usedTheorems, numSteps, diag := f diag }

/--
Result type for a simplification procedure. We have `pre` and `post` simplification procedures.
-/
inductive Step where
  /--
  For `pre` procedures, it returns the result without visiting any subexpressions.

  For `post` procedures, it returns the result.
  -/
  | done (r : Result)
  /--
  For `pre` procedures, the resulting expression is passed to `pre` again.

  For `post` procedures, the resulting expression is passed to `pre` again IF
  `Simp.Config.singlePass := false` and resulting expression is not equal to initial expression.
  -/
  | visit (e : Result)
  /--
  For `pre` procedures, continue transformation by visiting subexpressions, and then
  executing `post` procedures.

  For `post` procedures, this is equivalent to returning `visit`.
  -/
  | continue (e? : Option Result := none)
  deriving Inhabited

/--
A simplification procedure. Recall that we have `pre` and `post` procedures.
See `Step`.
-/
abbrev Simproc := Expr → SimpM Step

abbrev DStep := TransformStep

/--
Similar to `Simproc`, but resulting expression should be definitionally equal to the input one.
-/
abbrev DSimproc := Expr → SimpM DStep

def _root_.Lean.TransformStep.toStep (s : TransformStep) : Step :=
  match s with
  | .done e            => .done { expr := e }
  | .visit e           => .visit { expr := e }
  | .continue (some e) => .continue (some { expr := e })
  | .continue none     => .continue none

def mkEqTransResultStep (r : Result) (s : Step) : MetaM Step :=
  match s with
  | .done r'            => return .done (← mkEqTransOptProofResult r.proof? r.cache r')
  | .visit r'           => return .visit (← mkEqTransOptProofResult r.proof? r.cache r')
  | .continue none      => return .continue r
  | .continue (some r') => return .continue (some (← mkEqTransOptProofResult r.proof? r.cache r'))

/--
"Compose" the two given simplification procedures. We use the following semantics.
- If `f` produces `done` or `visit`, then return `f`'s result.
- If `f` produces `continue`, then apply `g` to new expression returned by `f`.

See `Simp.Step` type.
-/
@[always_inline]
def andThen (f g : Simproc) : Simproc := fun e => do
  match (← f e) with
  | .done r            => return .done r
  | .continue none     => g e
  | .continue (some r) => mkEqTransResultStep r (← g r.expr)
  | .visit r           => return .visit r

instance : AndThen Simproc where
  andThen s₁ s₂ := andThen s₁ (s₂ ())

@[always_inline]
def dandThen (f g : DSimproc) : DSimproc := fun e => do
  match (← f e) with
  | .done eNew            => return .done eNew
  | .continue none        => g e
  | .continue (some eNew) => g eNew
  | .visit eNew           => return .visit eNew

instance : AndThen DSimproc where
  andThen s₁ s₂ := dandThen s₁ (s₂ ())

/--
`Simproc` .olean entry.
-/
structure SimprocOLeanEntry where
  /-- Name of a declaration stored in the environment which has type `Simproc`. -/
  declName : Name
  post     : Bool := true
  keys     : Array SimpTheoremKey := #[]
  deriving Inhabited

/--
`Simproc` entry. It is the .olean entry plus the actual function.
-/
structure SimprocEntry extends SimprocOLeanEntry where
  /--
  Recall that we cannot store `Simproc` into .olean files because it is a closure.
  Given `SimprocOLeanEntry.declName`, we convert it into a `Simproc` by using the unsafe function `evalConstCheck`.
  -/
  proc : Sum Simproc DSimproc

abbrev SimprocTree := DiscrTree SimprocEntry

structure Simprocs where
  pre          : SimprocTree   := DiscrTree.empty
  post         : SimprocTree   := DiscrTree.empty
  simprocNames : PHashSet Name := {}
  erased       : PHashSet Name := {}
  deriving Inhabited

structure Methods where
  pre        : Simproc  := fun _ => return .continue
  post       : Simproc  := fun e => return .done { expr := e }
  dpre       : DSimproc := fun _ => return .continue
  dpost      : DSimproc := fun e => return .done e
  discharge? : Expr → SimpM (Option Expr) := fun _ => return none
  /--
  `wellBehavedDischarge` must **not** be set to `true` IF `discharge?`
  access local declarations with index >= `Context.lctxInitIndices` when
  `contextual := false`.
  Reason: it would prevent us from aggressively caching `simp` results.
  -/
  wellBehavedDischarge : Bool := true
  deriving Inhabited

unsafe def Methods.toMethodsRefImpl (m : Methods) : MethodsRef :=
  unsafeCast m

@[implemented_by Methods.toMethodsRefImpl]
opaque Methods.toMethodsRef (m : Methods) : MethodsRef

unsafe def MethodsRef.toMethodsImpl (m : MethodsRef) : Methods :=
  unsafeCast m

@[implemented_by MethodsRef.toMethodsImpl]
opaque MethodsRef.toMethods (m : MethodsRef) : Methods

def getMethods : SimpM Methods :=
  return MethodsRef.toMethods (← read)

def pre (e : Expr) : SimpM Step := do
  (← getMethods).pre e

def post (e : Expr) : SimpM Step := do
  (← getMethods).post e

@[inline] def getContext : SimpM Context :=
  readThe Context

def getConfig : SimpM Config :=
  return (← getContext).config

@[inline] def withParent (parent : Expr) (f : SimpM α) : SimpM α :=
  withTheReader Context (fun ctx => { ctx with parent? := parent }) f

def getSimpTheorems : SimpM SimpTheoremsArray :=
  return (← readThe Context).simpTheorems

def getSimpCongrTheorems : SimpM SimpCongrTheorems :=
  return (← readThe Context).congrTheorems

/--
Returns `true` if `simp` is in `dsimp` mode.
That is, only transformations that preserve definitional equality should be applied.
-/
def inDSimp : SimpM Bool :=
  return (← readThe Context).inDSimp

@[inline] def withPreservedCache (x : SimpM α) : SimpM α := do
  -- Recall that `cache.map₁` should be used linearly but `cache.map₂` is great for copies.
  let savedMap₂   := (← get).cache.map₂
  let savedStage₁ := (← get).cache.stage₁
  modify fun s => { s with cache := s.cache.switch }
  try x finally modify fun s => { s with cache.map₂ := savedMap₂, cache.stage₁ := savedStage₁ }

/--
Save current cache, reset it, execute `x`, and then restore original cache.
-/
@[inline] def withFreshCache (x : SimpM α) : SimpM α := do
  let cacheSaved := (← get).cache
  modify fun s => { s with cache := {} }
  try x finally modify fun s => { s with cache := cacheSaved }

@[inline] def withDischarger (discharge? : Expr → SimpM (Option Expr)) (wellBehavedDischarge : Bool) (x : SimpM α) : SimpM α :=
  withFreshCache <|
  withReader (fun r => { MethodsRef.toMethods r with discharge?, wellBehavedDischarge }.toMethodsRef) x

def recordTriedSimpTheorem (thmId : Origin) : SimpM Unit := do
  modifyDiag fun s =>
    let cNew := if let some c := s.triedThmCounter.find? thmId then c + 1 else 1
    { s with triedThmCounter := s.triedThmCounter.insert thmId cNew }

def recordSimpTheorem (thmId : Origin) : SimpM Unit := do
  modifyDiag fun s =>
    let cNew := if let some c := s.usedThmCounter.find? thmId then c + 1 else 1
    { s with usedThmCounter := s.usedThmCounter.insert thmId cNew }
  /-
  If `thmId` is an equational theorem (e.g., `foo.eq_1`), we should record `foo` instead.
  See issue #3547.
  -/
  let thmId ← match thmId with
    | .decl declName post false =>
      /-
      Remark: if `inv := true`, then the user has manually provided the theorem and wants to
      use it in the reverse direction. So, we only performs the substitution when `inv := false`
      -/
      if let some declName ← isEqnThm? declName then
        pure (Origin.decl declName post false)
      else
        pure thmId
    | _ => pure thmId
  modify fun s => { s with usedTheorems := s.usedTheorems.insert thmId }

def recordCongrTheorem (declName : Name) : SimpM Unit := do
  modifyDiag fun s =>
    let cNew := if let some c := s.congrThmCounter.find? declName then c + 1 else 1
    { s with congrThmCounter := s.congrThmCounter.insert declName cNew }

def recordTheoremWithBadKeys (thm : SimpTheorem) : SimpM Unit := do
  modifyDiag fun s =>
    -- check whether it is already there
    if unsafe s.thmsWithBadKeys.any fun thm' => ptrEq thm thm' then
      s
    else
      { s with thmsWithBadKeys := s.thmsWithBadKeys.push thm }

def Result.getProof (r : Result) : MetaM Expr := do
  match r.proof? with
  | some p => return p
  | none   => mkEqRefl r.expr

/--
  Similar to `Result.getProof`, but adds a `mkExpectedTypeHint` if `proof?` is `none`
  (i.e., result is definitionally equal to input), but we cannot establish that
  `source` and `r.expr` are definitionally when using `TransparencyMode.reducible`. -/
def Result.getProof' (source : Expr) (r : Result) : MetaM Expr := do
  match r.proof? with
  | some p => return p
  | none   =>
    if (← isDefEq source r.expr) then
      mkEqRefl r.expr
    else
      /- `source` and `r.expr` must be definitionally equal, but
         are not definitionally equal at `TransparencyMode.reducible` -/
      mkExpectedTypeHint (← mkEqRefl r.expr) (← mkEq source r.expr)

/-- Construct the `Expr` `cast h e`, from a `Simp.Result` with proof `h`. -/
def Result.mkCast (r : Simp.Result) (e : Expr) : MetaM Expr := do
  mkAppM ``cast #[← r.getProof, e]

def mkCongrFun (r : Result) (a : Expr) : MetaM Result :=
  match r.proof? with
  | none   => return { expr := mkApp r.expr a, proof? := none }
  | some h => return { expr := mkApp r.expr a, proof? := (← Meta.mkCongrFun h a) }

def mkCongr (r₁ r₂ : Result) : MetaM Result :=
  let e := mkApp r₁.expr r₂.expr
  match r₁.proof?, r₂.proof? with
  | none,     none   => return { expr := e, proof? := none }
  | some h,  none    => return { expr := e, proof? := (← Meta.mkCongrFun h r₂.expr) }
  | none,    some h  => return { expr := e, proof? := (← Meta.mkCongrArg r₁.expr h) }
  | some h₁, some h₂ => return { expr := e, proof? := (← Meta.mkCongr h₁ h₂) }

def mkImpCongr (src : Expr) (r₁ r₂ : Result) : MetaM Result := do
  let e := src.updateForallE! r₁.expr r₂.expr
  match r₁.proof?, r₂.proof? with
  | none,     none   => return { expr := e, proof? := none }
  | _,        _      => return { expr := e, proof? := (← Meta.mkImpCongr (← r₁.getProof) (← r₂.getProof)) } -- TODO specialize if bottleneck

/-- Given the application `e`, remove unnecessary casts of the form `Eq.rec a rfl` and `Eq.ndrec a rfl`. -/
partial def removeUnnecessaryCasts (e : Expr) : MetaM Expr := do
  let mut args := e.getAppArgs
  let mut modified := false
  for i in [:args.size] do
    let arg := args[i]!
    if isDummyEqRec arg then
      args := args.set! i (elimDummyEqRec arg)
      modified := true
  if modified then
    return mkAppN e.getAppFn args
  else
    return e
where
  isDummyEqRec (e : Expr) : Bool :=
    (e.isAppOfArity ``Eq.rec 6 || e.isAppOfArity ``Eq.ndrec 6) && e.appArg!.isAppOf ``Eq.refl

  elimDummyEqRec (e : Expr) : Expr :=
    if isDummyEqRec e then
      elimDummyEqRec e.appFn!.appFn!.appArg!
    else
      e

/--
Given a simplified function result `r` and arguments `args`, simplify arguments using `simp` and `dsimp`.
The resulting proof is built using `congr` and `congrFun` theorems.
-/
def congrArgs (r : Result) (args : Array Expr) : SimpM Result := do
  if args.isEmpty then
    return r
  else
    let cfg ← getConfig
    let infos := (← getFunInfoNArgs r.expr args.size).paramInfo
    let mut r := r
    let mut i := 0
    for arg in args do
      if h : i < infos.size then
        trace[Debug.Meta.Tactic.simp] "app [{i}] {infos.size} {arg} hasFwdDeps: {infos[i].hasFwdDeps}"
        let info := infos[i]
        if cfg.ground && info.isInstImplicit then
          -- We don't visit instance implicit arguments when we are reducing ground terms.
          -- Motivation: many instance implicit arguments are ground, and it does not make sense
          -- to reduce them if the parent term is not ground.
          -- TODO: consider using it as the default behavior.
          -- We have considered it at https://github.com/leanprover/lean4/pull/3151
          r ← mkCongrFun r arg
        else if !info.hasFwdDeps then
          r ← mkCongr r (← simp arg)
        else if (← whnfD (← inferType r.expr)).isArrow then
          r ← mkCongr r (← simp arg)
        else
          r ← mkCongrFun r (← dsimp arg)
      else if (← whnfD (← inferType r.expr)).isArrow then
        r ← mkCongr r (← simp arg)
      else
        r ← mkCongrFun r (← dsimp arg)
      i := i + 1
    return r

/--
Retrieve auto-generated congruence lemma for `f`.

Remark: If all argument kinds are `fixed` or `eq`, it returns `none` because
using simple congruence theorems `congr`, `congrArg`, and `congrFun` produces a more compact proof.
-/
def mkCongrSimp? (f : Expr) : SimpM (Option CongrTheorem) := do
  if f.isConst then if (← isMatcher f.constName!) then
    -- We always use simple congruence theorems for auxiliary match applications
    return none
  let info ← getFunInfo f
  let kinds ← getCongrSimpKinds f info
  if kinds.all fun k => match k with | CongrArgKind.fixed => true | CongrArgKind.eq => true | _ => false then
    /- See remark above. -/
    return none
  match (← get).congrCache[f]? with
  | some thm? => return thm?
  | none =>
    let thm? ← mkCongrSimpCore? f info kinds
    modify fun s => { s with congrCache := s.congrCache.insert f thm? }
    return thm?

/--
Try to use automatically generated congruence theorems. See `mkCongrSimp?`.
-/
def tryAutoCongrTheorem? (e : Expr) : SimpM (Option Result) := do
  let f := e.getAppFn
  -- TODO: cache
  let some cgrThm ← mkCongrSimp? f | return none
  if cgrThm.argKinds.size != e.getAppNumArgs then return none
  let args := e.getAppArgs
  let infos := (← getFunInfoNArgs f args.size).paramInfo
  let config ← getConfig
  let mut simplified := false
  let mut hasProof   := false
  let mut hasCast    := false
  let mut argsNew    := #[]
  let mut argResults := #[]
  let mut i          := 0 -- index at args
  for arg in args, kind in cgrThm.argKinds do
    if h : config.ground ∧ i < infos.size then
      if (infos[i]'h.2).isInstImplicit then
        -- Do not visit instance implicit arguments when `ground := true`
        -- See comment at `congrArgs`
        argsNew := argsNew.push arg
        i := i + 1
        continue
    match kind with
    | CongrArgKind.fixed =>
      let argNew ← dsimp arg
      if arg != argNew then
        simplified := true
      argsNew := argsNew.push argNew
    | CongrArgKind.cast  => hasCast := true; argsNew := argsNew.push arg
    | CongrArgKind.subsingletonInst => argsNew := argsNew.push arg
    | CongrArgKind.eq =>
      let argResult ← simp arg
      argResults := argResults.push argResult
      argsNew    := argsNew.push argResult.expr
      if argResult.proof?.isSome then hasProof := true
      if arg != argResult.expr then simplified := true
    | _ => unreachable!
    i := i + 1
  if !simplified then return some { expr := e }
  /-
    If `hasProof` is false, we used to return `mkAppN f argsNew` with `proof? := none`.
    However, this created a regression when we started using `proof? := none` for `rfl` theorems.
    Consider the following goal
    ```
    m n : Nat
    a : Fin n
    h₁ : m < n
    h₂ : Nat.pred (Nat.succ m) < n
    ⊢ Fin.succ (Fin.mk m h₁) = Fin.succ (Fin.mk m.succ.pred h₂)
    ```
    The term `m.succ.pred` is simplified to `m` using a `Nat.pred_succ` which is a `rfl` theorem.
    The auto generated theorem for `Fin.mk` has casts and if used here at `Fin.mk m.succ.pred h₂`,
    it produces the term `Fin.mk m (id (Eq.refl m) ▸ h₂)`. The key property here is that the
    proof `(id (Eq.refl m) ▸ h₂)` has type `m < n`. If we had just returned `mkAppN f argsNew`,
    the resulting term would be `Fin.mk m h₂` which is type correct, but later we would not be
    able to apply `eq_self` to
    ```lean
    Fin.succ (Fin.mk m h₁) = Fin.succ (Fin.mk m h₂)
    ```
    because we would not be able to establish that `m < n` and `Nat.pred (Nat.succ m) < n` are definitionally
    equal using `TransparencyMode.reducible` (`Nat.pred` is not reducible).
    Thus, we decided to return here only if the auto generated congruence theorem does not introduce casts.
  -/
  if !hasProof && !hasCast then
    return some { expr := mkAppN f argsNew }
  let mut proof := cgrThm.proof
  let mut type  := cgrThm.type
  let mut j := 0 -- index at argResults
  let mut subst := #[]
  for arg in args, argNew in argsNew, kind in cgrThm.argKinds do
    proof := mkApp proof arg
    type := type.bindingBody!
    match kind with
    | CongrArgKind.fixed =>
      /-
      We use `argNew` here because `dsimp` may have simplified the fixed argument.
      See issue #4339
      -/
      subst := subst.push argNew
    | CongrArgKind.cast  =>
      subst := subst.push arg
    | CongrArgKind.subsingletonInst =>
      subst := subst.push arg
      let clsNew := type.bindingDomain!.instantiateRev subst
      let instNew ← if (← isDefEq (← inferType arg) clsNew) then
        pure arg
      else
        match (← trySynthInstance clsNew) with
        | LOption.some val => pure val
        | _ =>
          trace[Meta.Tactic.simp.congr] "failed to synthesize instance{indentExpr clsNew}"
          return none
      proof := mkApp proof instNew
      subst := subst.push instNew
      type := type.bindingBody!
    | CongrArgKind.eq =>
      subst := subst.push arg
      let argResult := argResults[j]!
      let argProof ← argResult.getProof' arg
      j := j + 1
      proof := mkApp2 proof argResult.expr argProof
      subst := subst.push argResult.expr |>.push argProof
      type := type.bindingBody!.bindingBody!
    | _ => unreachable!
  let some (_, _, rhs) := type.instantiateRev subst |>.eq? | unreachable!
  let rhs ← if hasCast then removeUnnecessaryCasts rhs else pure rhs
  if hasProof then
    return some { expr := rhs, proof? := proof }
  else
    /- See comment above. This is reachable if `hasCast == true`. The `rhs` is not structurally equal to `mkAppN f argsNew` -/
    return some { expr := rhs }

def Result.addExtraArgs (r : Result) (extraArgs : Array Expr) : MetaM Result := do
  match r.proof? with
  | none => return { expr := mkAppN r.expr extraArgs }
  | some proof =>
    let mut proof := proof
    for extraArg in extraArgs do
      proof ← Meta.mkCongrFun proof extraArg
    return { expr := mkAppN r.expr extraArgs, proof? := some proof }

def Step.addExtraArgs (s : Step) (extraArgs : Array Expr) : MetaM Step := do
  match s with
  | .visit r => return .visit (← r.addExtraArgs extraArgs)
  | .done r => return .done (← r.addExtraArgs extraArgs)
  | .continue none => return .continue none
  | .continue (some r) => return .continue (← r.addExtraArgs extraArgs)

def DStep.addExtraArgs (s : DStep) (extraArgs : Array Expr) : DStep :=
  match s with
  | .visit eNew => .visit (mkAppN eNew extraArgs)
  | .done eNew => .done (mkAppN eNew extraArgs)
  | .continue none => .continue none
  | .continue (some eNew) => .continue (mkAppN eNew extraArgs)

def Result.addLambdas (r : Result) (xs : Array Expr) : MetaM Result := do
  let eNew ← mkLambdaFVars xs r.expr
  match r.proof? with
  | none   => return { expr := eNew }
  | some h =>
    let p ← xs.foldrM (init := h) fun x h => do
      mkFunExt (← mkLambdaFVars #[x] h)
    return { expr := eNew, proof? := p }

end Simp

export Simp (SimpM Simprocs)

/--
  Auxiliary method.
  Given the current `target` of `mvarId`, apply `r` which is a new target and proof that it is equal to the current one.
-/
def applySimpResultToTarget (mvarId : MVarId) (target : Expr) (r : Simp.Result) : MetaM MVarId := do
  match r.proof? with
  | some proof => mvarId.replaceTargetEq r.expr proof
  | none =>
    if target != r.expr then
      mvarId.replaceTargetDefEq r.expr
    else
      return mvarId

end Lean.Meta
