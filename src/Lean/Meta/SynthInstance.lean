/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Selsam, Leonardo de Moura

Type class instance synthesizer using tabled resolution.
-/
module
prelude
public import Init.Data.Array.InsertionSort
public import Lean.Meta.Instances
public import Lean.Meta.AbstractMVars
public import Lean.Meta.Check
import Lean.Util.CollectLevelMVars
import Lean.Util.ReplaceLevel
import Init.While

public section
namespace Lean.Meta

register_builtin_option synthInstance.maxHeartbeats : Nat := {
  defValue := 20000
  descr := "maximum amount of heartbeats per typeclass resolution problem. A heartbeat is number of (small) memory allocations (in thousands), 0 means no limit"
}

register_builtin_option synthInstance.maxSize : Nat := {
  defValue := 128
  descr := "maximum number of instances used to construct a solution in the type class instance synthesis procedure"
}

register_builtin_option backward.synthInstance.canonInstances : Bool := {
  defValue := true
  descr := "use optimization that relies on 'morally canonical' instances during type class resolution"
}

builtin_initialize synthInstanceCacheStatsEnabled : Bool ←
  return (← IO.getEnv "LEAN_SYNTH_CACHE_STATS").isSome

/-- Experiment: canonicalize the universe metavariables of the cache key. -/
builtin_initialize synthLevelNorm : Bool ←
  return (← IO.getEnv "LEAN_LEVEL_NORM").isSome

builtin_initialize synthDumpKey : Bool ←
  return (← IO.getEnv "LEAN_DUMP_KEY").isSome

/-- Log every completed type class lookup, to diff a normalized-key run against the baseline. -/
builtin_initialize synthTraceAll : Bool ←
  return (← IO.getEnv "LEAN_TRACE_SYNTH").isSome

/-- Experiment: canonicalize expression metavariables in the closure instead of bailing. -/
builtin_initialize synthMVarNorm : Bool ←
  return (← IO.getEnv "LEAN_MVAR_NORM").isSome

/-- The dependency-key ceiling analysis renormalizes on every miss and records into a process-global
reference from every search, which is far too expensive to leave on with the other statistics. -/
builtin_initialize synthDepEnabled : Bool ←
  return (← IO.getEnv "LEAN_SYNTH_DEP").isSome

builtin_initialize synthDumpSame : Bool ←
  return (← IO.getEnv "LEAN_SYNTH_DUMP_SAME").isSome

builtin_initialize synthDumpCtx : Bool ←
  return (← IO.getEnv "LEAN_SYNTH_DUMP_CTX").isSome


namespace SynthInstance

def getMaxHeartbeats (opts : Options) : Nat :=
  synthInstance.maxHeartbeats.get opts * 1000

structure Instance where
  val : Expr
  synthOrder : Array Nat
  deriving Inhabited

structure GeneratorNode where
  mvar            : Expr
  key             : Expr
  mctx            : MetavarContext
  instances       : Array Instance
  currInstanceIdx : Nat
  /--
  `typeHasMVars := true` if type of `mvar` contains metavariables.
  We store this information to implement an optimization that relies on the fact
  that instances are "morally canonical."
  That is, we need to find at most one answer for this generator node if the type
  does not have metavariables.
  -/
  typeHasMVars    : Bool
  deriving Inhabited

structure ConsumerNode where
  mvar     : Expr
  key      : Expr
  mctx     : MetavarContext
  subgoals : List Expr
  size     : Nat -- instance size so far
  deriving Inhabited

inductive Waiter where
  | consumerNode : ConsumerNode → Waiter
  | root         : Waiter

def Waiter.isRoot : Waiter → Bool
  | .consumerNode _ => false
  | .root           => true

/-!
  In tabled resolution, we creating a mapping from goals (e.g., `Coe Nat ?x`) to
  answers and waiters. Waiters are consumer nodes that are waiting for answers for a
  particular node.

  We implement this mapping using a `HashMap` where the keys are
  normalized expressions. That is, we replace assignable metavariables
  with auxiliary free variables of the form `_tc.<idx>`. We do
  not declare these free variables in any local context, and we should
  view them as "normalized names" for metavariables. For example, the
  term `f ?m ?m ?n` is normalized as
  `f _tc.0 _tc.0 _tc.1`.

  This approach is structural, and we may visit the same goal more
  than once if the different occurrences are just definitionally
  equal, but not structurally equal.

  Remark: a metavariable is assignable only if its depth is equal to
  the metavar context depth.
-/
namespace  MkTableKey

structure State where
  nextIdx : Nat := 0
  lmap    : Std.HashMap LMVarId Level := {}
  emap    : Std.HashMap MVarId Expr := {}
  mctx    : MetavarContext

abbrev M := StateM State

@[always_inline]
instance : MonadMCtx M where
  getMCtx := return (← get).mctx
  modifyMCtx f := modify fun s => { s with mctx := f s.mctx }

partial def normLevel (u : Level) : M Level := do
  if !u.hasMVar then
    return u
  else match u with
    | .succ v      => return u.updateSucc! (← normLevel v)
    | .max v w     => return u.updateMax! (← normLevel v) (← normLevel w)
    | .imax v w    => return u.updateIMax! (← normLevel v) (← normLevel w)
    | .mvar mvarId =>
      if (← getMCtx).getLevelDepth mvarId != (← getMCtx).depth then
        return u
      else
        let s ← get
        match (← get).lmap[mvarId]? with
        | some u' => pure u'
        | none    =>
          let u' := mkLevelParam <| Name.mkNum `_tc s.nextIdx
          modify fun s => { s with nextIdx := s.nextIdx + 1, lmap := s.lmap.insert mvarId u' }
          return u'
    | u => return u

partial def normExpr (e : Expr) : M Expr := do
  if !e.hasMVar then
    pure e
  else match e with
    | .const _ us      => return e.updateConst! (← us.mapM normLevel)
    | .sort u          => return e.updateSort! (← normLevel u)
    | .app f a         => return e.updateApp! (← normExpr f) (← normExpr a)
    | .letE _ t v b _  => return e.updateLetE! (← normExpr t) (← normExpr v) (← normExpr b)
    | .forallE _ d b _ => return e.updateForallE! (← normExpr d) (← normExpr b)
    | .lam _ d b _     => return e.updateLambdaE! (← normExpr d) (← normExpr b)
    | .mdata _ b       => return e.updateMData! (← normExpr b)
    | .proj _ _ b      => return e.updateProj! (← normExpr b)
    | .mvar mvarId     =>
      if !(← mvarId.isAssignable) then
        return e
      else
        let s ← get
        match s.emap[mvarId]? with
        | some e' => pure e'
        | none    => do
          let e' := mkFVar { name := Name.mkNum `_tc s.nextIdx }
          modify fun s => { s with nextIdx := s.nextIdx + 1, emap := s.emap.insert mvarId e' }
          return e'
    | _ => return e

end MkTableKey

/-- Remark: `mkTableKey` assumes `e` does not contain assigned metavariables. -/
def mkTableKey [Monad m] [MonadMCtx m] (e : Expr) : m Expr := do
  let (r, s) := MkTableKey.normExpr e |>.run { mctx := (← getMCtx) }
  setMCtx s.mctx
  return r

structure Answer where
  result     : AbstractMVarsResult
  resultType : Expr
  size       : Nat
  deriving Inhabited

structure TableEntry where
  waiters : Array Waiter
  answers : Array Answer := #[]

structure Context where
  maxResultSize : Nat
  maxHeartbeats : Nat

/--
  Remark: the SynthInstance.State is not really an extension of `Meta.State`.
  The field `postponed` is not needed, and the field `mctx` is misleading since
  `synthInstance` methods operate over different `MetavarContext`s simultaneously.
  That being said, we still use `extends` because it makes it simpler to move from
  `M` to `MetaM`.
-/
structure State where
  result?        : Option AbstractMVarsResult    := none
  generatorStack : Array GeneratorNode           := #[]
  resumeStack    : Array (ConsumerNode × Answer) := #[]
  tableEntries   : Std.HashMap Expr TableEntry   := {}

abbrev SynthM := ReaderT Context $ StateRefT State MetaM

def checkSystem : SynthM Unit := do
  Core.checkInterrupted
  Core.checkMaxHeartbeatsCore "typeclass" `synthInstance.maxHeartbeats (← read).maxHeartbeats

instance : Inhabited (SynthM α) where
  default := fun _ _ => default

/-- Return globals and locals instances that may unify with `type` -/
def getInstances (type : Expr) : MetaM (Array Instance) := do
  -- We must retrieve `localInstances` before we use `forallTelescopeReducing` because it will update the set of local instances
  let localInstances ← getLocalInstances
  forallTelescopeReducing type fun _ type => do
    let className? ← isClass? type
    match className? with
    | none   => throwError "type class instance expected{indentExpr type}"
    | some className =>
      if synthDepEnabled then
        synthDepCur.modify (·.insert className)
      let globalInstances ← getGlobalInstancesIndex
      let result ← globalInstances.getUnify type
      -- Using insertion sort because it is stable and the array `result` should be mostly sorted.
      -- Most instances have default priority.
      let result := result.insertionSort fun e₁ e₂ => e₁.priority < e₂.priority
      let erasedInstances ← getErasedInstances
      let env ← getEnv
      let mut result ← result.filterMapM fun e => match e.val with
        | .const constName us =>
          if erasedInstances.contains constName then
            return none
          else if env.isExporting && !env.contains constName then
            -- private instances must not leak into public scope
            return none
          else
            return some {
              val := e.val.updateConst! (← us.mapM (fun _ => mkFreshLevelMVar))
              synthOrder := e.synthOrder
            }
        | _ => panic! "global instance is not a constant"
      for linst in localInstances do
        if linst.className == className then
          let synthOrder ← forallTelescopeReducing (← inferType linst.fvar) fun xs _ => do
            if xs.isEmpty then return #[]
            let mut order := #[]
            for i in *...xs.size, x in xs do
              if (← getFVarLocalDecl x).binderInfo == .instImplicit then
                order := order.push i
            return order
          result := result.push { val := linst.fvar, synthOrder }
      trace[Meta.synthInstance.instances] result.map (·.val)
      return result

def mkGeneratorNode? (key mvar : Expr) : MetaM (Option GeneratorNode) := do
  let mvarType  ← inferType mvar
  let mvarType  ← instantiateMVars mvarType
  let instances ← getInstances mvarType
  if instances.isEmpty then
    return none
  else
    let mctx ← getMCtx
    return some {
      mvar, key, mctx, instances
      typeHasMVars := mvarType.hasMVar
      currInstanceIdx := instances.size
    }

/--
  Create a new generator node for `mvar` and add `waiter` as its waiter.
  `key` must be `mkTableKey mctx mvarType`. -/
def newSubgoal (mctx : MetavarContext) (key : Expr) (mvar : Expr) (waiter : Waiter) : SynthM Unit :=
  withMCtx mctx do withTraceNode' `Meta.synthInstance do
    match (← mkGeneratorNode? key mvar) with
    | none      => pure ((), m!"no instances for {key}")
    | some node =>
      let entry : TableEntry := { waiters := #[waiter] }
      modify fun s =>
       { s with
         generatorStack := s.generatorStack.push node
         tableEntries   := s.tableEntries.insert key entry }
      pure ((), m!"new goal {key}")

def findEntry? (key : Expr) : SynthM (Option TableEntry) := do
  return (← get).tableEntries[key]?

def getEntry (key : Expr) : SynthM TableEntry := do
  match (← findEntry? key) with
  | none       => panic! "invalid key at synthInstance"
  | some entry => pure entry

/--
  Create a `key` for the goal associated with the given metavariable.
  That is, we create a key for the type of the metavariable.

  We must instantiate assigned metavariables before we invoke `mkTableKey`. -/
def mkTableKeyFor (mctx : MetavarContext) (mvar : Expr) : SynthM Expr :=
  withMCtx mctx do
    let mvarType ← inferType mvar
    let mvarType ← instantiateMVars mvarType
    mkTableKey mvarType

/-- See `getSubgoals` and `getSubgoalsAux`

   We use the parameter `j` to reduce the number of `instantiate*` invocations.
   It is the same approach we use at `forallTelescope` and `lambdaTelescope`.
   Given `getSubgoalsAux args j subgoals instVal type`,
   we have that `type.instantiateRevRange j args.size args` does not have loose bound variables. -/
structure SubgoalsResult where
  subgoals     : List Expr
  instVal      : Expr
  instTypeBody : Expr

/--
  `getSubgoals lctx localInsts xs inst` creates the subgoals for the instance `inst`.
  The subgoals are in the context of the free variables `xs`, and
  `(lctx, localInsts)` is the local context and instances before we added the free variables to it.

  This extra complication is required because
    1- We want all metavariables created by `synthInstance` to share the same local context.
    2- We want to ensure that applications such as `mvar xs` are higher order patterns.

  The method `getGoals` create a new metavariable for each parameter of `inst`.
  For example, suppose the type of `inst` is `forall (x_1 : A_1) ... (x_n : A_n), B x_1 ... x_n`.
  Then, we create the metavariables `?m_i : forall xs, A_i`, and return the subset of these
  metavariables that are instance implicit arguments, and the expressions:
    - `inst (?m_1 xs) ... (?m_n xs)` (aka `instVal`)
    - `B (?m_1 xs) ... (?m_n xs)` -/
def getSubgoals (lctx : LocalContext) (localInsts : LocalInstances) (xs : Array Expr) (inst : Instance) : MetaM SubgoalsResult := do
  let mut instVal := inst.val
  let mut instType ← inferType instVal
  let mut mvars := #[]
  let mut subst := #[]
  repeat do
    if let .forallE _ d b _ := instType then
      let d := d.instantiateRev subst
      let mvar ← mkFreshExprMVarAt lctx localInsts (← mkForallFVars xs d)
      subst := subst.push (mkAppN mvar xs)
      instVal := mkApp instVal (mkAppN mvar xs)
      instType := b
      mvars := mvars.push mvar
    else
      instType ← whnf (instType.instantiateRev subst)
      instVal := instVal.instantiateRev subst
      subst := #[]
      unless instType.isForall do break
  return {
    instVal := instVal.instantiateRev subst
    instTypeBody := instType.instantiateRev subst
    subgoals := inst.synthOrder.map (mvars[·]!) |>.toList
  }

/--
  Try to synthesize metavariable `mvar` using the instance `inst`.
  Remark: `mctx` is set using `withMCtx`.
  If it succeeds, the result is a new updated metavariable context and a new list of subgoals.
  A subgoal is created for each instance implicit parameter of `inst`. -/
def tryResolve (mvar : Expr) (inst : Instance) : MetaM (Option (MetavarContext × List Expr)) := do
  if (← isDiagnosticsEnabled) then
    if let .const declName _ := inst.val.getAppFn then
      recordInstance declName
  let mvarType   ← inferType mvar
  let lctx       ← getLCtx
  let localInsts ← getLocalInstances
  forallTelescopeReducing mvarType fun xs mvarTypeBody => do
    let { subgoals, instVal, instTypeBody } ← getSubgoals lctx localInsts xs inst
    withTraceNode `Meta.synthInstance.tryResolve (fun _ => do withMCtx (← getMCtx) do
        return m!"{← instantiateMVars mvarTypeBody} ≟ {← instantiateMVars instTypeBody}") do
    if (← isDefEq mvarTypeBody instTypeBody) then
      /-
      We set `etaReduce := true`.
      For example, suppose `e` is the local variable `inst x y`, and `xs` is `#[x, y]`, then
      the result is `inst` instead of `fun x y => inst x y`.

      Consider the following definition.
      ```
      def filter (p : α → Prop) [inst : DecidablePred p] (xs : List α) : List α :=
        match xs with
        | [] => []
        | x :: xs' => if p x then x :: filter p xs' else filter p xs'
      ```
      Without `etaReduce := true`, the implicit instance at the `filter` applications would be `fun x => inst x` instead of `inst`.
      Moreover, the equation lemmas associated with `filter` would have `fun x => inst x` on their right-hand-side. Then,
      we would start getting terms such as `fun x => (fun x => inst x) x` when using the equational theorem.
      -/
      let instVal ← mkLambdaFVars xs instVal (etaReduce := true)
      /-
      When the goal type is metavariable-free, we assign `instVal` directly: the final
      `isDefEq mvar instVal` recheck is redundant (the goal type and `instTypeBody` have
      just been unified, and the type of `instVal` is `instTypeBody` by construction) and
      can be very expensive, since it re-infers the type of `instVal` and re-unifies it
      with the goal type.

      When the goal type contains metavariables, re-unifying the two (definitionally equal, but not
      necessarily syntactically equal) types has side effects that elaboration relies on.
      In particular, `isDefEqArgs` runs `trySynthPending` on metavariables in
      instance-implicit argument positions of the applications it descends into. Example:
      the goal `IsPredArchimedean ι ?pre ?pd` (from Mathlib) — created when elaborating a class
      projection, whose class parameters are demoted to plain implicit binders — matches a
      candidate by assigning the candidate's fresh metavariables to `?pre`/`?pd` without
      determining them. No other component is responsible for these metavariables, and the
      recheck's `trySynthPending` is what synthesizes them; without it, the answer is
      parametric in `?pd` and elaboration fails with "don't know how to synthesize
      implicit argument" (see `tests/elab/synthPendingClassMVars.lean`).

      Moreover, the set of metavariables the recheck synthesizes is not a function of the
      goal alone: `isDefEqArgs` only descends into subterms whose two spellings differ
      (e.g. rechecking `C (f a ?m) =?= C (f a' ?m)` pends `?m` iff `a` and `a'` are
      syntactically different), so the side effects cannot be replayed after a direct
      assignment, which has only one spelling. Explicit replacements fail in both
      directions: synthesizing all pending class metavariables in the goal breaks stage2
      (`Init/Internal/Order/Basic.lean`: a higher-order `[Nonempty ε]` metavariable inside
      the goal's subject argument must be left to unification), and synthesizing none
      breaks Mathlib (`Mathlib/Order/SuccPred/LinearLocallyFinite.lean`). Hence we keep
      the recheck whenever the goal type contains metavariables.

      **Note**: We should consider eliminating this nasty side effect and fixing
      Mathlib in the few places that rely on it. There are ~10 such places.

      Remark: we check only `mvarTypeBody`. The goal's hypotheses could contain
      metavariables too, but checking the body is cheaper and good enough in practice,
      and we want to remove this check altogether (see note above).
      -/
      if !(← instantiateMVars mvarTypeBody).hasExprMVar then
        -- Remark: `mvar` is not assigned here: `tryResolve` runs on the generator node's
        -- metavariable context snapshot, in which `mvar` is fresh.
        mvar.mvarId!.assign instVal
      else
        unless (← isDefEq mvar instVal) do return none
      return some ((← getMCtx), subgoals)
    return none

/--
  Assign a precomputed answer to `mvar`.
  If it succeeds, the result is a new updated metavariable context and a new list of subgoals. -/
def tryAnswer (mctx : MetavarContext) (mvar : Expr) (answer : Answer) : SynthM (Option MetavarContext) :=
  withMCtx mctx do
    let (_, _, val) ← openAbstractMVarsResult answer.result
    if (← isDefEq mvar val) then
      return some (← getMCtx)
    else
      return none

/-- Move waiters that are waiting for the given answer to the resume stack. -/
def wakeUp (answer : Answer) : Waiter → SynthM Unit
  | .root               => do
    /- Recall that we now use `ignoreLevelMVarDepth := true`. Thus, we should allow solutions
       containing universe metavariables, and not check `answer.result.paramNames.isEmpty`.
       We use `openAbstractMVarsResult` to construct the universe metavariables
       at the correct depth. -/
    if answer.result.numMVars == 0 then
      modify fun s => { s with result? := answer.result }
    else
      let (_, _, answerExpr) ← openAbstractMVarsResult answer.result
      trace[Meta.synthInstance] "skip answer containing metavariables {answerExpr}"
  | .consumerNode cNode =>
    modify fun s => { s with resumeStack := s.resumeStack.push (cNode, answer) }

def isNewAnswer (oldAnswers : Array Answer) (answer : Answer) : Bool :=
  oldAnswers.all fun oldAnswer =>
    -- Remark: isDefEq here is too expensive. TODO: if `==` is too imprecise, add some light normalization to `resultType` at `addAnswer`
    -- iseq ← isDefEq oldAnswer.resultType answer.resultType; pure (!iseq)
    oldAnswer.resultType != answer.resultType

private def mkAnswer (cNode : ConsumerNode) : MetaM Answer :=
  withMCtx cNode.mctx do
    let val ← instantiateMVars cNode.mvar
    trace[Meta.synthInstance.newAnswer] "size: {cNode.size}, val: {val}"
    let result ← abstractMVars val -- assignable metavariables become parameters
    let resultType ← inferType result.expr
    return { result, resultType, size := cNode.size + 1 }

/--
  Create a new answer after `cNode` resolved all subgoals.
  That is, `cNode.subgoals == []`.
  And then, store it in the tabled entries map, and wakeup waiters. -/
def addAnswer (cNode : ConsumerNode) : SynthM Unit := do
  withMCtx cNode.mctx do
  if cNode.size ≥ (← read).maxResultSize then
    trace[Meta.synthInstance.answer] "{crossEmoji} {← instantiateMVars (← inferType cNode.mvar)}{Format.line}(size: {cNode.size} ≥ {(← read).maxResultSize})"
  else
    withTraceNode `Meta.synthInstance.answer
      (fun _ => return m!"{← instantiateMVars (← inferType cNode.mvar)}") do
    let answer ← mkAnswer cNode
    -- Remark: `answer` does not contain assignable or assigned metavariables.
    let key := cNode.key
    let { waiters, answers } ← getEntry key
    if isNewAnswer answers answer then
      let newEntry := { waiters, answers := answers.push answer }
      modify fun s => { s with tableEntries := s.tableEntries.insert key newEntry }
      waiters.forM (wakeUp answer)

/--
  Return `true` if a type of the form `(a_1 : A_1) → ... → (a_n : A_n) → B` has an unused argument `a_i`.

  Remark: This is syntactic check and no reduction is performed.
-/
private def hasUnusedArguments : Expr → Bool
  | .forallE _ _ b _ => !b.hasLooseBVar 0 || hasUnusedArguments b
  | _ => false

/--
  If the type of the metavariable `mvar` has unused argument, return a pair `(α, transformer)`
  where `α` is a new type without the unused arguments and the `transformer` is a function for converting a
  solution with type `α` into a value that can be assigned to `mvar`.
  Example: suppose `mvar` has type `(a : A) → (b : B a) → (c : C a) → D a c`, the result is the pair
  ```
  ((a : A) → (c : C a) → D a c,
   fun (f : (a : A) → (c : C a) → D a c) (a : A) (b : B a) (c : C a) => f a c
  )
  ```

  This method is used to improve the effectiveness of the TC resolution procedure. It was suggested and prototyped by
  Tomas Skrivan. It improves the support for instances of type `a : A → C` where `a` does not appear in class `C`.
  When we look for such an instance it is enough to look for an instance `c : C` and then return `fun _ => c`.

  Tomas' approach makes sure that instance of a type like `a : A → C` never gets tabled/cached. More on that later.
  At the core is this method. it takes an expression E and does two things:

  The modification to TC resolution works this way: We are looking for an instance of `E`, if it is tabled
  just get it as normal, but if not first remove all unused arguments producing `E'`. Now we look up the table again but
  for `E'`. If it exists, use the transformer to create E. If it does not exists, create a new goal `E'`.
-/
private def removeUnusedArguments? (mctx : MetavarContext) (mvar : Expr) : MetaM (Option (Expr × Expr)) :=
  withMCtx mctx do
    let mvarType ← instantiateMVars (← inferType mvar)
    if !hasUnusedArguments mvarType then
      return none
    else
      forallTelescope mvarType fun xs body => do
        let ys ← xs.foldrM (init := []) fun x ys => do
          if body.containsFVar x.fvarId! then
            return x :: ys
          else if (← ys.anyM fun y => return (← inferType y).containsFVar x.fvarId!) then
            return x :: ys
          else
            return ys
        let ys := ys.toArray
        let mvarType' ← mkForallFVars ys body
        withLocalDeclD `redf mvarType' fun f => do
          let transformer ← mkLambdaFVars #[f] (← mkLambdaFVars xs (mkAppN f ys) (etaReduce := true)) (etaReduce := true)
          trace[Meta.synthInstance.unusedArgs] "{mvarType}\nhas unused arguments, reduced type{indentExpr mvarType'}\nTransformer{indentExpr transformer}"
          return some (mvarType', transformer)

/-- Process the next subgoal in the given consumer node. -/
def consume (cNode : ConsumerNode) : SynthM Unit := do
  /- Filter out subgoals that have already been assigned when solving typing constraints.
    This may happen when a local instance type depends on other local instances.
    For example, in Mathlib, we have
    ```
    @Submodule.setLike : {R : Type u_1} → {M : Type u_2} →
      [_inst_1 : Semiring R] →
      [_inst_2 : AddCommMonoid M] →
      [_inst_3 : @ModuleS R M _inst_1 _inst_2] →
      SetLike (@Submodule R M _inst_1 _inst_2 _inst_3) M
    ```
  -/
  let cNode := { cNode with
    subgoals := ← withMCtx cNode.mctx do
      cNode.subgoals.filterM (not <$> ·.mvarId!.isAssigned)
  }
  match cNode.subgoals with
  | []      => addAnswer cNode
  | mvar::_ =>
     let waiter := Waiter.consumerNode cNode
     let key ← mkTableKeyFor cNode.mctx mvar
     let entry? ← findEntry? key
     match entry? with
     | none       =>
       -- Remove unused arguments and try again, see comment at `removeUnusedArguments?`
       match (← removeUnusedArguments? cNode.mctx mvar) with
       | none => newSubgoal cNode.mctx key mvar waiter
       | some (mvarType', transformer) =>
         let key' ← withMCtx cNode.mctx <| mkTableKey mvarType'
         match (← findEntry? key') with
         | none =>
           let (mctx', mvar') ← withMCtx cNode.mctx do
             let mvar' ← mkFreshExprMVar mvarType'
             return (← getMCtx, mvar')
           newSubgoal mctx' key' mvar' (Waiter.consumerNode { cNode with mctx := mctx', subgoals := mvar'::cNode.subgoals })
         | some entry' =>
           let answers' ← entry'.answers.mapM fun a => withMCtx cNode.mctx do
             let trAnswr := Expr.betaRev transformer #[← instantiateMVars a.result.expr]
             let trAnswrType ← inferType trAnswr
             pure { a with result.expr := trAnswr, resultType := trAnswrType }
           modify fun s =>
             { s with
               resumeStack  := answers'.foldl (fun s answer => s.push (cNode, answer)) s.resumeStack,
               tableEntries := s.tableEntries.insert key' { entry' with waiters := entry'.waiters.push waiter } }
     | some entry => modify fun s =>
       { s with
         resumeStack  := entry.answers.foldl (fun s answer => s.push (cNode, answer)) s.resumeStack,
         tableEntries := s.tableEntries.insert key { entry with waiters := entry.waiters.push waiter } }

def getTop : SynthM GeneratorNode :=
  return (← get).generatorStack.back!

@[inline] def modifyTop (f : GeneratorNode → GeneratorNode) : SynthM Unit :=
  modify fun s => { s with generatorStack := s.generatorStack.modify (s.generatorStack.size - 1) f }

/-- Try the next instance in the node on the top of the generator stack. -/
def generate : SynthM Unit := do
  let gNode ← getTop
  if gNode.currInstanceIdx == 0  then
    modify fun s => { s with generatorStack := s.generatorStack.pop }
  else
    let key  := gNode.key
    let idx  := gNode.currInstanceIdx - 1
    let inst := gNode.instances[idx]!
    let mctx := gNode.mctx
    let mvar := gNode.mvar
    /- See comment at `typeHasMVars` -/
    if backward.synthInstance.canonInstances.get (← getOptions) then
      unless gNode.typeHasMVars do
        if let some entry := (← get).tableEntries[key]? then
          if entry.answers.any fun answer => answer.result.numMVars == 0 then
            /-
            We already have an answer that:
              1. its result does not have metavariables.
              2. its types do not have metavariables.

            Thus, we can skip other solutions because we assume instances are "morally canonical".
            We have added this optimization to address issue #3996.

            Remark: Condition 1 is important since root nodes only take into account results
            that do **not** contain metavariables. This extra check was added to address issue #4213.
            -/
            modify fun s => { s with generatorStack := s.generatorStack.pop }
            return
    discard do withMCtx mctx do
      withTraceNode `Meta.synthInstance.apply
        (fun _ => return m!"apply {inst.val} to {← instantiateMVars (← inferType mvar)}") do
      modifyTop fun gNode => { gNode with currInstanceIdx := idx }
      if let some (mctx, subgoals) ← tryResolve mvar inst then
        consume { key, mvar, subgoals, mctx, size := 0 }
        return some ()
      return none

def getNextToResume : SynthM (ConsumerNode × Answer) := do
  let r := (← get).resumeStack.back!
  modify fun s => { s with resumeStack := s.resumeStack.pop }
  return r

/--
  Given `(cNode, answer)` on the top of the resume stack, continue execution by using `answer` to solve the
  next subgoal. -/
def resume : SynthM Unit := do
  let (cNode, answer) ← getNextToResume
  match cNode.subgoals with
  | []         => panic! "resume found no remaining subgoals"
  | mvar::rest =>
    match (← tryAnswer cNode.mctx mvar answer) with
    | none      => return ()
    | some mctx =>
      withMCtx mctx do
      let goal    ← inferType cNode.mvar
      let subgoal ← inferType mvar
      withTraceNode `Meta.synthInstance.resume
        (fun _ => withMCtx cNode.mctx do
          return m!"propagating {← instantiateMVars answer.resultType} to subgoal {← instantiateMVars subgoal} of {← instantiateMVars goal}") do
      trace[Meta.synthInstance.resume] "size: {cNode.size + answer.size}"
      consume { key := cNode.key, mvar := cNode.mvar, subgoals := rest, mctx, size := cNode.size + answer.size }

def step : SynthM Bool := do
  checkSystem
  let s ← get
  if !s.resumeStack.isEmpty then
    resume
    return true
  else if !s.generatorStack.isEmpty then
    generate
    return true
  else
    return false

def getResult : SynthM (Option AbstractMVarsResult) :=
  return (← get).result?

partial def synth : SynthM (Option AbstractMVarsResult) := do
  if (← step) then
    match (← getResult) with
    | none        => synth
    | some result => return result
  else
    return none

def main (type : Expr) (maxResultSize : Nat) : MetaM (Option AbstractMVarsResult) :=
  withCurrHeartbeats do
     let mvar ← mkFreshExprMVar type
     let key  ← mkTableKey type
     let action : SynthM (Option AbstractMVarsResult) := do
       newSubgoal (← getMCtx) key mvar Waiter.root
       synth
     tryCatchRuntimeEx
       (action.run { maxResultSize := maxResultSize, maxHeartbeats := getMaxHeartbeats (← getOptions) } |>.run' {})
       fun ex =>
         if ex.isRuntime then
           throwError "failed to synthesize{indentExpr type}\n{ex.toMessageData}{useDiagnosticMsg}"
         else
           throw ex

end SynthInstance

/-!
Type class parameters can be annotated with `outParam` annotations.

Given `C a_1 ... a_n`, we replace `a_i` with a fresh metavariable `?m_i` IF
`a_i` is an `outParam`.
The result is type correct because we reject type class declarations IF
it contains a regular parameter X that depends on an `out` parameter Y.

Then, we execute type class resolution as usual.
If it succeeds, and metavariables ?m_i have been assigned, we try to unify
the original type `C a_1 ... a_n` with the normalized one.
-/

/-- Result kind for `preprocess` -/
private inductive PreprocessKind where
  | /--
    Target type does not have metavariables.
    We use the type to construct the cache key even if the class has output parameters.
    Reason: we want to avoid the normalization step in this case.
    -/
    noMVars
  | /-- Target type has metavariables, and class does not have output parameters. -/
    mvarsNoOutputParams
  | /-- Target type has metavariables, and class has output parameters. -/
    mvarsOutputParams

/-- Return type for `preprocess` -/
private structure PreprocessResult where
  type         : Expr
  cacheKeyType : Expr := type
  kind         : PreprocessKind

/--
Returns `{ type, cacheKeyType, hasOutParams }`, where `type` is the normalized type, and `cacheKeyType`
is part of the key for the type class resolution cache. If the class associated with `type`
does not have output parameters, then, `cacheKeyType` is `type`.
If it has, we replace arguments corresponding with output parameters with wildcard terms.

For example, the cache key for a query like
`HAppend.{0, 0, ?u} (BitVec 8) (BitVec 8) ?m` should be independent of the specific
metavariable IDs in output parameter positions. To achieve this, output parameter arguments
are erased from the cache key. However, universe levels that only appear in output parameter
types (e.g., `?u` corresponding to the result type's universe) must also be erased to avoid
cache misses when the same query is issued with different universe metavariable IDs.
-/
private def preprocess (type : Expr) : MetaM PreprocessResult :=
  let keyExprWildcard := mkFVar { name := `__wild__  }
  let keyLevelWildcard := mkLevelParam `__wild__
  forallTelescopeReducing type fun xs typeBody => do
    let typeBody ← whnf typeBody
    let type ← mkForallFVars xs typeBody
    if !type.hasMVar then return { type, kind := .noMVars }
    /-
    **Note**: Workaround for classes such as `class ToLevel.{u}`. They do not have any parameters,
    the universe parameter inference engine at `Class.lean` assumes `u` is an output parameter,
    but this is not correct. We can remove this check after we update `Class.lean` and perform an
    update stage0
    -/
    if typeBody.isConst then return { type, kind := .mvarsNoOutputParams }
    let c := typeBody.getAppFn
    let .const declName us := c | return { type, kind := .mvarsNoOutputParams }
    let env ← getEnv
    let some outParamsPos := getOutParamPositions? env declName | return { type, kind := .mvarsNoOutputParams }
    let some outLevelParamPos := getOutLevelParamPositions? env declName | unreachable!
    if outParamsPos.isEmpty && outLevelParamPos.isEmpty then return { type, kind := .mvarsNoOutputParams }
    let c := if outLevelParamPos.isEmpty then c else
      let rec normLevels (us : List Level) (i : Nat) : List Level :=
        match us with
        | [] => []
        | u :: us =>
          let u := if i ∈ outLevelParamPos then keyLevelWildcard else u
          u :: normLevels us (i+1)
      mkConst declName (normLevels us 0)
    let rec norm (e : Expr) (i : Nat) : Expr :=
      match e with
      | .app f a =>
        let a := if i ∈ outParamsPos then keyExprWildcard else a
        mkApp (norm f (i-1)) a
      | _ => c
    let typeBody := norm typeBody (typeBody.getAppNumArgs - 1)
    let cacheKeyType ← mkForallFVars xs typeBody
    return { type, cacheKeyType, kind := .mvarsOutputParams }

private partial def preprocessOutParam (type : Expr) : MetaM Expr :=
  forallTelescope type fun xs typeBody => do
    /- **Note**: See similar test at preprocess. -/
    if typeBody.isConst then return type
    let c := typeBody.getAppFn
    let .const declName us := c | return type
    let env ← getEnv
    let some outParamsPos := getOutParamPositions? env declName | return type
    let some outLevelParamPos := getOutLevelParamPositions? env declName | unreachable!
    if outParamsPos.isEmpty && outLevelParamPos.isEmpty then return type
    let c ← if outLevelParamPos.isEmpty then pure c else
      -- Replace universe parameters corresponding to output parameters with fresh universe metavariables.
      let rec preprocessLevels (us : List Level) (i : Nat) : MetaM (List Level) := do
        match us with
        | [] => return []
        | u :: us =>
          let u ← if i ∈ outLevelParamPos then mkFreshLevelMVar else pure u
          let us ← preprocessLevels us (i+1)
          return u :: us
      pure <| mkConst declName (← preprocessLevels us 0)
    let rec preprocessArgs (type : Expr) (i : Nat) (args : Array Expr) : MetaM (Array Expr) := do
      if h : i < args.size then
        let type ← whnf type
        match type with
        | .forallE _ d b _ => do
          let arg := args[i]
          /-
          We should not simply check `d.isOutParam`. See `checkOutParam` and issue #1852.
          If an instance implicit argument depends on an `outParam`, it is treated as an `outParam` too.
          -/
          let arg ← if outParamsPos.contains i then mkFreshExprMVar d else pure arg
          let args := args.set i arg
          preprocessArgs (b.instantiate1 arg) (i+1) args
        | _ =>
          throwError "type class resolution failed, insufficient number of arguments" -- TODO improve error message
      else
        return args
    let args := typeBody.getAppArgs
    if outParamsPos.isEmpty then
      mkForallFVars xs (mkAppN c args)
    else
      let cType ← inferType c
      let args ← preprocessArgs cType 0 args
      mkForallFVars xs (mkAppN c args)

/-!
  Remark: when `maxResultSize? == none`, the configuration option `synthInstance.maxResultSize` is used.
  Remark: we use a different option for controlling the maximum result size for coercions.
-/

private def assignOutParams (type : Expr) (result : Expr) : MetaM Bool := do
  let resultType ← inferType result
  /-
  Output parameters of local instances may be marked as `syntheticOpaque` by the application-elaborator.
  We use `withAssignableSyntheticOpaque` to make sure this kind of parameter can be assigned by the following `isDefEq`.
  TODO: rewrite this check to avoid `withAssignableSyntheticOpaque`.

  **Note**: We tried to remove `withDefault` at the following `isDefEq` because it was a potential performance footgun. TC is supposed to unfold only `reducible` definitions and `instances`.
  We reverted the change because it triggered thousands of failures related to the `OrderDual` type. Example:
  ```
  variable {ι : Type}
  def OrderDual (α : Type) : Type := α
  instance [I : DecidableEq ι] : DecidableEq (OrderDual ι) := inferInstance -- Failure
  ```
  Mathlib developers are currently trying to refactor the `OrderDual` declaration,
  but it will take time. We will try to remove the `withDefault` again after the refactoring.
  -/
  let defEq ← withDefault <| withAssignableSyntheticOpaque <| isDefEq type resultType
  unless defEq do
    trace[Meta.synthInstance] "{crossEmoji} result type{indentExpr resultType}\nis not definitionally equal to{indentExpr type}"
  return defEq

/--
Auxiliary function for converting the `AbstractMVarsResult` returned by `SynthInstance.main` into an `Expr`.
-/
private def applyAbstractResult? (type : Expr) (abstResult? : Option AbstractMVarsResult) : MetaM (Option Expr) := do
  let some abstResult := abstResult? | return none
  let (_, _, result) ← openAbstractMVarsResult abstResult
  unless (← assignOutParams type result) do return none
  let result ← instantiateMVars result
  /- We use `check` to propagate universe constraints implied by the `result`.
      Recall that we use `allowLevelAssignments := true` which allows universe metavariables in the current depth to be assigned,
      but these assignments are discarded by `withNewMCtxDepth`.

      TODO: If this `check` is a performance bottleneck, we can improve performance by tracking whether
            a universe metavariable from previous universe levels have been assigned or not during TC resolution.
            We only need to perform the `check` if this kind of assignment have been performed.

      The example in the issue #796 exposed this issue.
      ```
      structure A
      class B (a : outParam A) (α : Sort u)
      class C {a : A} (α : Sort u) [B a α]
      class D {a : A} (α : Sort u) [B a α] [c : C α]
      class E (a : A) where [c (α : Sort u) [B a α] : C α]
      instance c {a : A} [e : E a] (α : Sort u) [B a α] : C α := e.c α

      def d {a : A} [e : E a] (α : Sort u) [b : B a α] : D α := ⟨⟩
      ```
      The term `D α` has two instance implicit arguments. The second one has type `C α`, and TC
      resolution produces the result `@c.{u} a e α b`.
      Note that the `e` has type `E.{?v} a`, and `E` is universe polymorphic,
      but the universe does not occur in the parameter `a`. We have that `?v := u` is implied by `@c.{u} a e α b`,
      but this assignment is lost.
  -/
  check result
  return some result

/--
Statistics for the type class resolution cache, collected per process when the
`LEAN_SYNTH_CACHE_STATS` environment variable is set. `hitPersistent`/`hitTransient` count lookups
served by the persistent env-extension tier and the transient `Meta.Cache` tier respectively;
`insertPersistent`/`insertTransient` count new entries routed to each tier.
-/
structure SynthInstanceCacheStats where
  hitPersistent    : Nat := 0
  hitTransient     : Nat := 0
  miss             : Nat := 0
  insertPersistent : Nat := 0
  insertTransient  : Nat := 0
  -- Misses broken down by the query's `PreprocessKind` (concrete vs metavariable-laden).
  missNoMVars      : Nat := 0
  missMVarsNoOut   : Nat := 0
  missMVarsOut     : Nat := 0
  -- Misses that reached `cacheResult` (i.e. did not throw `isDefEqStuck`), by kind. Per kind,
  -- `stuck = miss<kind> - cached<kind>`.
  cachedNoMVars    : Nat := 0
  cachedMVarsNoOut : Nat := 0
  cachedMVarsOut   : Nat := 0
  -- Of the cached misses: whether an instance was found or a failure was memoized.
  cachedFound      : Nat := 0
  cachedFailed     : Nat := 0
  -- Heartbeats consumed by the search itself, split by kind × outcome (stuck = threw
  -- `isDefEqStuck`; cached = completed). Measures how *expensive* each miss category is.
  missStuckHbNoMV      : Nat := 0
  missStuckHbMVNoOut   : Nat := 0
  missStuckHbMVOut     : Nat := 0
  missDoneHbNoMV     : Nat := 0
  missDoneHbMVNoOut  : Nat := 0
  missDoneHbMVOut    : Nat := 0
  -- Cached (completed) search heartbeats split by whether an instance was found or a failure memoized.
  hbFound          : Nat := 0
  hbFailed         : Nat := 0
  -- `.noMVars` lookups whose free-variable normalization bailed (a closure variable is let-bound or
  -- mvar-typed), so the query fell back to a raw, context-specific key.
  normBail         : Nat := 0
  normBailMiss     : Nat := 0
  -- Cost of the free-variable normalization, which runs on every `.noMVars` lookup because its
  -- result is the key, and so is paid by the lookups that hit as well.
  normCalls          : Nat := 0
  normHb             : Nat := 0
  -- Local instance closures served from / written to `Meta.Cache.synthNormClosure`, and, summed
  -- over the builds, the closure size, the number of local instances, and the closure variables
  -- whose raw `LocalDecl.type` has a metavariable (the ones a memo hit must revalidate).
  normMemoHits       : Nat := 0
  normMemoBuilds     : Nat := 0
  -- Why a miss missed, by the fate of its *exact* key. `first`: never queried before.
  -- `neverIns`: queried before, but that search never produced a cache entry (it got stuck, or its
  -- result escaped the normalization closure). `insT`/`insP`: an entry *was* inserted before, into
  -- the transient / persistent tier, and is gone.
  missKeyFirst       : Nat := 0
  missKeyNeverIns    : Nat := 0
  missKeyInsT        : Nat := 0
  missKeyInsP        : Nat := 0
  missKeyFirstHb     : Nat := 0
  missKeyNeverInsHb  : Nat := 0
  missKeyInsTHb      : Nat := 0
  missKeyInsPHb      : Nat := 0
  -- Searches whose result escaped the normalization closure, so nothing was cached at all.
  abstractSkip       : Nat := 0
  normClosureSize    : Nat := 0
  normLocalInsts     : Nat := 0
  normMVarTypedDecls : Nat := 0
  -- `normBail` split by cause.
  bailNotFound     : Nat := 0
  bailMVarType     : Nat := 0
  -- Query-type shape of misses: ground (no fvar/mvar, maximally reusable), fvarOnly (fvars but no
  -- mvar — `.noMVars` yet local-context-bound, so the key never recurs), hasMVar.
  missGround       : Nat := 0
  missFVarOnly     : Nat := 0
  missHasMVar      : Nat := 0
  -- "Blocker" analysis: for a miss, how many would become a HIT under the given relaxation of the
  -- key (some cached entry agrees on everything the relaxation does not drop). A miss can count
  -- under several. `blkNone` = no relaxation helps, i.e. a genuinely unseen query.
  --
  -- `blkLocalInsts` is vacuous under fvar normalization: `BEq LocalInstance` compares only the
  -- `fvar`, and normalized local instances sit at canonical positions, so the component agrees
  -- regardless of the actual instances. The local-instance context lives in `normFVarTypes`
  -- instead; `blkLocalCtx` drops both together and is the meaningful measurement.
  blkLocalInsts    : Nat := 0
  blkDepth         : Nat := 0
  blkScoped        : Nat := 0
  blkLocalAttr     : Nat := 0
  blkMaxSize       : Nat := 0
  blkCanon         : Nat := 0
  blkExporting     : Nat := 0
  -- `localInsts` and `normFVarTypes` dropped jointly.
  blkLocalCtx      : Nat := 0
  -- `type` with metavariable ids / universe levels / both canonicalized by first occurrence.
  blkTypeMVar      : Nat := 0
  blkTypeLevel     : Nat := 0
  blkTypeNorm      : Nat := 0
  -- Ceiling: every context component dropped *and* the type mvar/level-normalized. Counts misses
  -- whose type was already searched for in this process, under any context.
  blkCeil          : Nat := 0
  -- Absolute ceiling: as `blkCeil`, but free variables in the type are canonicalized too, so this
  -- counts misses whose bare *skeleton* recurs. Unsound as a key (`.noMVars` queries with raw
  -- fvars only match up to the local context, which this drops); an upper bound only.
  blkSkeleton      : Nat := 0
  -- Sound target: as the fvar normalization, but applied to metavariable-laden keys too (their
  -- type, metavariables, universes and local instances canonicalized together; see
  -- `StatsNorm.runCtx`). What extending the normalization beyond `.noMVars` could recover.
  blkNormCtx       : Nat := 0
  -- `blkNormCtx` split by the query's `PreprocessKind`, to locate the recoverable cost. Only
  -- `.mvarsOutputParams` queries can have their metavariables assigned by the search, so only
  -- those need the assignment recorded alongside the cached result.
  blkNormCtxNoMV     : Nat := 0
  blkNormCtxMVNoOut  : Nat := 0
  blkNormCtxMVOut    : Nat := 0
  -- Upper bound: every variable subterm conflated. Bounds what *any* key normalization could
  -- recover, and checks the analysis: see `blkInconsistent`.
  -- Free variables of the type and local instances canonicalized, metavariables and universes left
  -- as they are: the *sound* normalization we already apply to `.noMVars`, extended to the
  -- metavariable-laden keys, which currently carry raw free variables and so never share.
  blkFVarCtx       : Nat := 0
  blkConflate      : Nat := 0
  -- Misses matched by `blkSkeleton` but not by the strictly looser `blkConflate`. Must be 0; a
  -- nonzero value means a relaxation leaves some key component in place and the numbers are wrong.
  blkInconsistent  : Nat := 0
  -- Every lookup, split by whether it was served from the cache and by whether the *response* it
  -- produced had already been produced in this process. The response is canonicalized (free
  -- variables, metavariables and universes) so that the same instance in different contexts counts
  -- as the same response. A miss whose response was already known is a search that recomputed an
  -- answer the process had; it is the work a perfect cache would remove, independently of how the
  -- key is shaped. `respNs` is wall-clock nanoseconds.
  -- For a miss that recomputed a known answer: which components of the key differ from the key of
  -- the lookup that first produced that answer. A miss can differ in several. `wDiffTypeOnly` means
  -- only the query type differs, i.e. two genuinely different queries share an answer and no
  -- relaxation of the *context* could have recovered it; `wDiffCtxOnly` means the query type is
  -- identical and only the context differs, i.e. the key discriminates on something the answer does
  -- not depend on.
  wDiffType        : Nat := 0
  wDiffLocalInsts  : Nat := 0
  wDiffFVarTypes   : Nat := 0
  wDiffFVarValues  : Nat := 0
  wDiffDepth       : Nat := 0
  wDiffScoped      : Nat := 0
  wDiffLocalAttr   : Nat := 0
  wDiffMaxSize     : Nat := 0
  wDiffCanon       : Nat := 0
  wDiffTransp      : Nat := 0
  wDiffExporting   : Nat := 0
  -- Of the wasted misses whose `type` differs: how many still differ after a context-independent
  -- re-canonicalization. If this is small, the types are structurally the same and only the
  -- canonical numbering shifted (which it does when the local-instance closure differs), so the
  -- real discriminator is the context, not the query.
  -- Dependency-validated key: only the local instances of classes the search actually consulted.
  -- `depConflict` is the self-check: it must stay 0, or the dependency key is unsound.
  -- Wasted misses that are the SAME query as the one that first produced the answer, once the
  -- metavariables of that earlier query are instantiated: i.e. the same query asked twice at
  -- different stages of elaboration.
  wSameAfterInst   : Nat := 0
  wSameAfterInstHb : Nat := 0
  levelNormKeys    : Nat := 0
  levelNormMVars   : Nat := 0
  depRecov         : Nat := 0
  depRecovHb       : Nat := 0
  depRecovNs       : Nat := 0
  depConflict      : Nat := 0
  depNoNorm        : Nat := 0
  depInstsKept     : Nat := 0
  depInstsTotal    : Nat := 0
  wDiffTypeSkel    : Nat := 0
  wDiffTypeOnly    : Nat := 0
  wDiffCtxOnly     : Nat := 0
  wDiffNothing     : Nat := 0
  wDiffTypeOnlyNs  : Nat := 0
  wDiffCtxOnlyNs   : Nat := 0
  -- Of `missRespSeen`: how many recomputed a *failure* rather than an instance.
  missRespSeenFail : Nat := 0
  missRespSeenFailNs : Nat := 0
  hitRespSeen      : Nat := 0
  hitRespNew       : Nat := 0
  missRespSeen     : Nat := 0
  missRespNew      : Nat := 0
  hitRespSeenHb    : Nat := 0
  hitRespNewHb     : Nat := 0
  missRespSeenHb   : Nat := 0
  missRespNewHb    : Nat := 0
  hitRespSeenNs    : Nat := 0
  hitRespNewNs     : Nat := 0
  missRespSeenNs   : Nat := 0
  missRespNewNs    : Nat := 0
  blkNone          : Nat := 0
  -- Search heartbeats spent on the misses counted by each `blk*` field above: weights each blocker
  -- by the cost of the searches it would recover if that relaxation were applied.
  blkLocalInstsHb  : Nat := 0
  blkDepthHb       : Nat := 0
  blkScopedHb      : Nat := 0
  blkLocalAttrHb   : Nat := 0
  blkMaxSizeHb     : Nat := 0
  blkCanonHb       : Nat := 0
  blkExportingHb   : Nat := 0
  blkLocalCtxHb    : Nat := 0
  blkTypeMVarHb    : Nat := 0
  blkTypeLevelHb   : Nat := 0
  blkTypeNormHb    : Nat := 0
  blkCeilHb        : Nat := 0
  blkSkeletonHb    : Nat := 0
  blkNormCtxHb     : Nat := 0
  blkNormCtxHbNoMV    : Nat := 0
  blkNormCtxHbMVNoOut : Nat := 0
  blkNormCtxHbMVOut   : Nat := 0
  blkFVarCtxHb     : Nat := 0
  blkConflateHb    : Nat := 0
  blkNoneHb        : Nat := 0
  deriving Inhabited

builtin_initialize synthInstanceCacheStatsRef : IO.Ref SynthInstanceCacheStats ← IO.mkRef {}

/-- Number of relaxations tracked by `blankedKeyHashes` / the `blk*` fields. -/
private def numBlockers := 16

/-- Fingerprints of every consolidated response already produced in this process. -/
builtin_initialize synthResponseSeen : IO.Ref (Std.HashSet UInt64) ← IO.mkRef {}

/-- For each response, the key of the lookup that first produced it. -/
builtin_initialize synthResponseKey : IO.Ref (Std.HashMap UInt64 SynthInstanceCacheKey) ← IO.mkRef {}

/-- Hashes of every exact key ever looked up, and of those ever inserted into each tier. -/
builtin_initialize synthKeyQueried : IO.Ref (Std.HashSet UInt64) ← IO.mkRef {}
builtin_initialize synthKeyInsertedT : IO.Ref (Std.HashSet UInt64) ← IO.mkRef {}
builtin_initialize synthKeyInsertedP : IO.Ref (Std.HashSet UInt64) ← IO.mkRef {}

/-- Per-relaxation sets of blanked-key hashes of cached entries, for the blocker analysis (index
matches `blankedKeyHashes`). -/
builtin_initialize synthKeyBlankAux : IO.Ref (Array (Std.HashSet UInt64)) ←
  IO.mkRef (Array.replicate numBlockers {})

namespace StatsNorm

/--
Canonicalizes the free-variable, metavariable and universe-level identities occurring in a
cache-key type, so that two queries differing only in `?m` ids, fvar ids or universe parameter
names hash alike. Measurement only: the resulting canonical identifiers denote nothing.
-/
structure State where
  fvars   : Std.HashMap FVarId Nat := {}
  mvars   : Std.HashMap MVarId Nat := {}
  lmvars  : Std.HashMap LMVarId Nat := {}
  lparams : Std.HashMap Name Nat := {}
  nextLvl : Nat := 0

private def canonFVar (i : Nat) : Expr := .fvar ⟨.mkNum `_snx i⟩
private def canonMVar (i : Nat) : Expr := .mvar ⟨.mkNum `_snm i⟩
private def canonLevel (i : Nat) : Level := .param (.mkNum `_snu i)

private def normLevel (l : Level) : StateM State Level := do
  match l with
  | .zero => return l
  | .succ a => return .succ (← normLevel a)
  | .max a b => return .max (← normLevel a) (← normLevel b)
  | .imax a b => return .imax (← normLevel a) (← normLevel b)
  | .param n =>
    match (← get).lparams[n]? with
    | some i => return canonLevel i
    | none =>
      let i := (← get).nextLvl
      modify fun s => { s with lparams := s.lparams.insert n i, nextLvl := i + 1 }
      return canonLevel i
  | .mvar m =>
    match (← get).lmvars[m]? with
    | some i => return canonLevel i
    | none =>
      let i := (← get).nextLvl
      modify fun s => { s with lmvars := s.lmvars.insert m i, nextLvl := i + 1 }
      return canonLevel i

private def normMVar (m : MVarId) : StateM State Expr := do
  match (← get).mvars[m]? with
  | some i => return canonMVar i
  | none =>
    let i := (← get).mvars.size
    modify fun s => { s with mvars := s.mvars.insert m i }
    return canonMVar i

private def normFVar (x : FVarId) : StateM State Expr := do
  match (← get).fvars[x]? with
  | some i => return canonFVar i
  | none =>
    let i := (← get).fvars.size
    modify fun s => { s with fvars := s.fvars.insert x i }
    return canonFVar i

private partial def normExpr (fvars mvars levels : Bool) (e : Expr) : StateM State Expr := do
  let lvl (l : Level) : StateM State Level := if levels then normLevel l else pure l
  let go := normExpr fvars mvars levels
  match e with
  | .fvar x => if fvars then normFVar x else pure e
  | .mvar m => if mvars then normMVar m else pure e
  | .sort l => return .sort (← lvl l)
  | .const n us => return .const n (← us.mapM lvl)
  | .app f a => return .app (← go f) (← go a)
  | .lam n t b bi => return .lam n (← go t) (← go b) bi
  | .forallE n t b bi => return .forallE n (← go t) (← go b) bi
  | .letE n t v b nd => return .letE n (← go t) (← go v) (← go b) nd
  | .mdata d b => return .mdata d (← go b)
  | .proj s i b => return .proj s i (← go b)
  | _ => return e

/-- `normExpr` run on a fresh state. -/
def run (fvars mvars levels : Bool) (e : Expr) : Expr :=
  (normExpr fvars mvars levels e).run' {}

/--
Replaces *every* free variable, metavariable and universe by one shared token, conflating variables
that positional canonicalization keeps apart. Strictly looser than `run true true true`, so it must
match whenever that does: a miss counted under `blkSkeleton` but not under `blkConflate` is
impossible, and indicates a relaxation that fails to drop some component of the key. Such misses are
counted in `blkInconsistent`, which is the analysis checking itself.
-/
partial def conflateAll (e : Expr) : Expr :=
  let lvl (_ : Level) : Level := .param `_snc
  match e with
  | .fvar _           => .fvar ⟨`_snc⟩
  | .mvar _           => .mvar ⟨`_snc⟩
  | .sort l           => .sort (lvl l)
  | .const n us       => .const n (us.map lvl)
  | .app f a          => .app (conflateAll f) (conflateAll a)
  | .lam n d b bi     => .lam n (conflateAll d) (conflateAll b) bi
  | .forallE n d b bi => .forallE n (conflateAll d) (conflateAll b) bi
  | .letE n t v b nd  => .letE n (conflateAll t) (conflateAll v) (conflateAll b) nd
  | .mdata m b        => .mdata m (conflateAll b)
  | .proj st i b      => .proj st i (conflateAll b)
  | e                 => e

/--
Canonicalizes `type` and the local instances together, in first-occurrence order starting from
`type`, and tags each local instance with its class name (which `BEq LocalInstance` ignores) so
that contexts offering different instances stay apart.

This models extending the free-variable normalization to metavariable-laden queries, whose keys are
currently stored raw.
-/
def runCtxFVarOnly (k : SynthInstanceCacheKey) : SynthInstanceCacheKey := Id.run do
  let go : StateM State (Expr × LocalInstances × Array Expr) := do
    let type ← normExpr true false false k.type
    let insts ← k.localInsts.mapM fun li => do
      return { li with fvar := ← normExpr true false false li.fvar }
    return (type, insts, insts.map fun li => .const li.className [])
  let (type, insts, classNames) := go.run' {}
  return { k with type, localInsts := insts, normFVarTypes := k.normFVarTypes ++ classNames }

def runCtx (k : SynthInstanceCacheKey) : SynthInstanceCacheKey := Id.run do
  let go : StateM State (Expr × LocalInstances × Array Expr) := do
    let type ← normExpr true true true k.type
    let insts ← k.localInsts.mapM fun li => do
      return { li with fvar := ← normExpr true true true li.fvar }
    return (type, insts, insts.map fun li => .const li.className [])
  let (type, insts, classNames) := go.run' {}
  return { k with type, localInsts := insts, normFVarTypes := k.normFVarTypes ++ classNames }

end StatsNorm

/--
The key under each tracked relaxation, hashed. Index order matches the `blk*` fields:
0 localInsts, 1 synthPendingDepth, 2 activeScopedInsts, 3 localAttrInsts, 4 maxResultSize,
5 canonInstances, 6 isExporting, 7 localInsts+normFVarTypes, 8 type mvar-normalized,
9 type level-normalized, 10 type mvar+level-normalized, 11 every context component dropped and
the type mvar+level-normalized, 12 as 11 but with the type's free variables canonicalized too,
13 type and local instances jointly canonicalized (`StatsNorm.runCtx`), keeping the context.
-/
private def blankedKeyHashes (k : SynthInstanceCacheKey) : Array UInt64 :=
  let tNorm := StatsNorm.run false true true k.type
  let bare : SynthInstanceCacheKey → SynthInstanceCacheKey := fun k =>
    { k with localInsts := #[], normFVarTypes := #[], normFVarValues := #[], synthPendingDepth := none,
             activeScopedInsts := #[], localAttrInsts := #[], maxResultSize := 0,
             canonInstances := false, isExporting := false,
             respectTransparency := false, respectTransparencyTypes := false }
  #[hash { k with localInsts := #[] },
    hash { k with synthPendingDepth := none },
    hash { k with activeScopedInsts := #[] },
    hash { k with localAttrInsts := #[] },
    hash { k with maxResultSize := 0 },
    hash { k with canonInstances := false },
    hash { k with isExporting := false },
    hash { k with localInsts := #[], normFVarTypes := #[], normFVarValues := #[] },
    hash { k with type := StatsNorm.run false true false k.type },
    hash { k with type := StatsNorm.run false false true k.type },
    hash { k with type := tNorm },
    hash (bare { k with type := tNorm }),
    hash (bare { k with type := StatsNorm.run true true true k.type }),
    hash (StatsNorm.runCtx k),
    hash (bare { k with type := StatsNorm.conflateAll k.type }),
    hash (StatsNorm.runCtxFVarOnly k)]

@[inline] private def recordSynthInstanceCacheStat (f : SynthInstanceCacheStats → SynthInstanceCacheStats) :
    MetaM Unit := do
  if synthInstanceCacheStatsEnabled then
    synthInstanceCacheStatsRef.modify f

/-- Adds `d` to the heartbeat counter for the miss's key class (see `missKeyFirst`). -/
@[inline] private def addKeyClassHb (cls : Nat) (d : Nat) (s : SynthInstanceCacheStats) : SynthInstanceCacheStats :=
  match cls with
  | 0 => { s with missKeyFirstHb := s.missKeyFirstHb + d }
  | 1 => { s with missKeyNeverInsHb := s.missKeyNeverInsHb + d }
  | 2 => { s with missKeyInsTHb := s.missKeyInsTHb + d }
  | _ => { s with missKeyInsPHb := s.missKeyInsPHb + d }

/-- Adds the miss's search heartbeats `d` to each blocker-weighted counter whose relaxation is set.
`bits` indexes as in `blankedKeyHashes`; `blkNone` means no relaxation would recover this miss. -/
@[inline] private def addBlockerHb (kind : PreprocessKind) (bits : Array Bool) (blkNone : Bool) (d : Nat) (s : SynthInstanceCacheStats) : SynthInstanceCacheStats :=
  let s := if bits[0]! then { s with blkLocalInstsHb := s.blkLocalInstsHb + d } else s
  let s := if bits[1]! then { s with blkDepthHb := s.blkDepthHb + d } else s
  let s := if bits[2]! then { s with blkScopedHb := s.blkScopedHb + d } else s
  let s := if bits[3]! then { s with blkLocalAttrHb := s.blkLocalAttrHb + d } else s
  let s := if bits[4]! then { s with blkMaxSizeHb := s.blkMaxSizeHb + d } else s
  let s := if bits[5]! then { s with blkCanonHb := s.blkCanonHb + d } else s
  let s := if bits[6]! then { s with blkExportingHb := s.blkExportingHb + d } else s
  let s := if bits[7]! then { s with blkLocalCtxHb := s.blkLocalCtxHb + d } else s
  let s := if bits[8]! then { s with blkTypeMVarHb := s.blkTypeMVarHb + d } else s
  let s := if bits[9]! then { s with blkTypeLevelHb := s.blkTypeLevelHb + d } else s
  let s := if bits[10]! then { s with blkTypeNormHb := s.blkTypeNormHb + d } else s
  let s := if bits[11]! then { s with blkCeilHb := s.blkCeilHb + d } else s
  let s := if bits[12]! then { s with blkSkeletonHb := s.blkSkeletonHb + d } else s
  let s := if bits[14]! then { s with blkConflateHb := s.blkConflateHb + d } else s
  let s := if bits[15]! then { s with blkFVarCtxHb := s.blkFVarCtxHb + d } else s
  let s := if bits[13]! then
      let s := { s with blkNormCtxHb := s.blkNormCtxHb + d }
      match kind with
      | .noMVars             => { s with blkNormCtxHbNoMV := s.blkNormCtxHbNoMV + d }
      | .mvarsNoOutputParams => { s with blkNormCtxHbMVNoOut := s.blkNormCtxHbMVNoOut + d }
      | .mvarsOutputParams   => { s with blkNormCtxHbMVOut := s.blkNormCtxHbMVOut + d }
    else s
  if blkNone then { s with blkNoneHb := s.blkNoneHb + d } else s

/-- Records the heartbeats consumed by a search that threw `isDefEqStuck`, by query kind. -/
@[inline] private def recordMissStuckHeartbeats (kind : PreprocessKind) (bits : Array Bool) (blkNone : Bool) (cls : Nat) (hb0 : Nat) : MetaM Unit := do
  if synthInstanceCacheStatsEnabled then
    let d := (← IO.getNumHeartbeats) - hb0
    synthInstanceCacheStatsRef.modify fun s =>
      let s := match kind with
        | .noMVars             => { s with missStuckHbNoMV := s.missStuckHbNoMV + d }
        | .mvarsNoOutputParams => { s with missStuckHbMVNoOut := s.missStuckHbMVNoOut + d }
        | .mvarsOutputParams   => { s with missStuckHbMVOut := s.missStuckHbMVOut + d }
      addKeyClassHb cls d (addBlockerHb kind bits blkNone d s)

/-- Records the heartbeats consumed by a completed (cached) search, by query kind and found/failed. -/
@[inline] private def recordMissDoneHeartbeats (kind : PreprocessKind) (found : Bool) (bits : Array Bool) (blkNone : Bool) (cls : Nat) (hb0 : Nat) : MetaM Unit := do
  if synthInstanceCacheStatsEnabled then
    let d := (← IO.getNumHeartbeats) - hb0
    synthInstanceCacheStatsRef.modify fun s =>
      let s := addKeyClassHb cls d (addBlockerHb kind bits blkNone d s)
      let s := match kind with
        | .noMVars             => { s with missDoneHbNoMV := s.missDoneHbNoMV + d }
        | .mvarsNoOutputParams => { s with missDoneHbMVNoOut := s.missDoneHbMVNoOut + d }
        | .mvarsOutputParams   => { s with missDoneHbMVOut := s.missDoneHbMVOut + d }
      if found then { s with hbFound := s.hbFound + d } else { s with hbFailed := s.hbFailed + d }

/-- Adds `key`'s blanked-key hashes to the blocker-analysis sets. -/
private def recordBlankedKey (key : SynthInstanceCacheKey) : MetaM Unit := do
  if synthInstanceCacheStatsEnabled then
    let hs := blankedKeyHashes key
    synthKeyBlankAux.modify fun a => Id.run do
      let mut a := a
      for i in *...hs.size do
        a := a.set! i ((a[i]!).insert hs[i]!)
      return a

/--
Classifies a miss by the fate of its exact key: 0 never queried before, 1 queried but never cached,
2 an entry was inserted into the transient tier, 3 into the persistent tier. Records the key as
queried.
-/
private def classifyMissKey (key : SynthInstanceCacheKey) : MetaM Nat := do
  let h := hash key
  let cls ←
    if !(← synthKeyQueried.get).contains h then pure 0
    else if (← synthKeyInsertedP.get).contains h then pure 3
    else if (← synthKeyInsertedT.get).contains h then pure 2
    else pure 1
  synthKeyQueried.modify (·.insert h)
  recordSynthInstanceCacheStat fun s => match cls with
    | 0 => { s with missKeyFirst := s.missKeyFirst + 1 }
    | 1 => { s with missKeyNeverIns := s.missKeyNeverIns + 1 }
    | 2 => { s with missKeyInsT := s.missKeyInsT + 1 }
    | _ => { s with missKeyInsP := s.missKeyInsP + 1 }
  return cls

/-- On a miss, records the query-type shape and which relaxation(s) of the key would have turned it
into a hit. Returns `(bits, blkNone)` (see `addBlockerHb`) for heartbeat-weighting.

The miss's own blanked keys are recorded afterwards, so a relaxation counts as a blocker whenever
the relaxed key was *queried* before, whether or not that query produced a cache entry. Searches
that end in `isDefEqStuck` never reach `cacheResult`, and would otherwise be invisible here. -/
private def recordMissAnalysis (kind : PreprocessKind) (type : Expr) (key : SynthInstanceCacheKey) :
    MetaM (Array Bool × Bool) := do
  if synthInstanceCacheStatsEnabled then
    let hs := blankedKeyHashes key
    let aux ← synthKeyBlankAux.get
    let bits := Array.ofFn (n := numBlockers) fun i => aux[i]!.contains hs[i]!
    let hasM := type.hasMVar; let hasF := type.hasFVar
    let blkNone := !bits.any id
    synthInstanceCacheStatsRef.modify fun s =>
      let s := if hasM then { s with missHasMVar := s.missHasMVar + 1 }
               else if hasF then { s with missFVarOnly := s.missFVarOnly + 1 }
               else { s with missGround := s.missGround + 1 }
      let s := if bits[0]! then { s with blkLocalInsts := s.blkLocalInsts + 1 } else s
      let s := if bits[1]! then { s with blkDepth := s.blkDepth + 1 } else s
      let s := if bits[2]! then { s with blkScoped := s.blkScoped + 1 } else s
      let s := if bits[3]! then { s with blkLocalAttr := s.blkLocalAttr + 1 } else s
      let s := if bits[4]! then { s with blkMaxSize := s.blkMaxSize + 1 } else s
      let s := if bits[5]! then { s with blkCanon := s.blkCanon + 1 } else s
      let s := if bits[6]! then { s with blkExporting := s.blkExporting + 1 } else s
      let s := if bits[7]! then { s with blkLocalCtx := s.blkLocalCtx + 1 } else s
      let s := if bits[8]! then { s with blkTypeMVar := s.blkTypeMVar + 1 } else s
      let s := if bits[9]! then { s with blkTypeLevel := s.blkTypeLevel + 1 } else s
      let s := if bits[10]! then { s with blkTypeNorm := s.blkTypeNorm + 1 } else s
      let s := if bits[11]! then { s with blkCeil := s.blkCeil + 1 } else s
      let s := if bits[12]! then { s with blkSkeleton := s.blkSkeleton + 1 } else s
      let s := if bits[13]! then
          let s := { s with blkNormCtx := s.blkNormCtx + 1 }
          match kind with
          | .noMVars             => { s with blkNormCtxNoMV := s.blkNormCtxNoMV + 1 }
          | .mvarsNoOutputParams => { s with blkNormCtxMVNoOut := s.blkNormCtxMVNoOut + 1 }
          | .mvarsOutputParams   => { s with blkNormCtxMVOut := s.blkNormCtxMVOut + 1 }
        else s
      let s := if bits[14]! then { s with blkConflate := s.blkConflate + 1 } else s
      let s := if bits[15]! then { s with blkFVarCtx := s.blkFVarCtx + 1 } else s
      let s := if bits[12]! && !bits[14]! then { s with blkInconsistent := s.blkInconsistent + 1 } else s
      if blkNone then { s with blkNone := s.blkNone + 1 } else s
    recordBlankedKey key
    return (bits, blkNone)
  else
    return (#[], false)


/--
If `LEAN_SYNTH_CACHE_STATS` is set, prints a per-module TSV line with the accumulated cache
statistics to stderr; see `SynthInstanceCacheStats`. Called once at the end of a frontend run.
-/
def reportSynthInstanceCacheStats (mod : Name) : IO Unit := do
  if synthInstanceCacheStatsEnabled then
    let s ← synthInstanceCacheStatsRef.get
    let lookups := s.hitPersistent + s.hitTransient + s.miss
    IO.eprintln s!"SYNTHCACHE\t{mod}\tlookups={lookups}\thitP={s.hitPersistent}\t\
      hitT={s.hitTransient}\tmiss={s.miss}\tinsP={s.insertPersistent}\tinsT={s.insertTransient}\t\
      missNoMV={s.missNoMVars}\tmissMVNoOut={s.missMVarsNoOut}\tmissMVOut={s.missMVarsOut}\t\
      cachedNoMV={s.cachedNoMVars}\tcachedMVNoOut={s.cachedMVarsNoOut}\tcachedMVOut={s.cachedMVarsOut}\t\
      found={s.cachedFound}\tfailed={s.cachedFailed}\t\
      missStuckHbNoMV={s.missStuckHbNoMV}\tmissStuckHbMVNoOut={s.missStuckHbMVNoOut}\tmissStuckHbMVOut={s.missStuckHbMVOut}\t\
      missDoneHbNoMV={s.missDoneHbNoMV}\tmissDoneHbMVNoOut={s.missDoneHbMVNoOut}\tmissDoneHbMVOut={s.missDoneHbMVOut}\t\
      hbFound={s.hbFound}\thbFailed={s.hbFailed}\t\
      missGround={s.missGround}\tmissFVarOnly={s.missFVarOnly}\tmissHasMVar={s.missHasMVar}\t\
      normBail={s.normBail}\tnormBailMiss={s.normBailMiss}\t\
      normCalls={s.normCalls}\tnormHb={s.normHb}\tnormMemoHits={s.normMemoHits}\t\
      normMemoBuilds={s.normMemoBuilds}\tnormClosureSize={s.normClosureSize}\t\
      missKeyFirst={s.missKeyFirst}\tmissKeyNeverIns={s.missKeyNeverIns}\t\
      missKeyInsT={s.missKeyInsT}\tmissKeyInsP={s.missKeyInsP}\t\
      missKeyFirstHb={s.missKeyFirstHb}\tmissKeyNeverInsHb={s.missKeyNeverInsHb}\t\
      missKeyInsTHb={s.missKeyInsTHb}\tmissKeyInsPHb={s.missKeyInsPHb}\t\
      abstractSkip={s.abstractSkip}\t\
      normLocalInsts={s.normLocalInsts}\tnormMVarTypedDecls={s.normMVarTypedDecls}\t\
      bailNotFound={s.bailNotFound}\tbailMVarType={s.bailMVarType}\t\
      blkLocalInsts={s.blkLocalInsts}\tblkDepth={s.blkDepth}\tblkScoped={s.blkScoped}\t\
      blkLocalAttr={s.blkLocalAttr}\tblkMaxSize={s.blkMaxSize}\tblkCanon={s.blkCanon}\t\
      blkExporting={s.blkExporting}\tblkLocalCtx={s.blkLocalCtx}\tblkTypeMVar={s.blkTypeMVar}\t\
      blkTypeLevel={s.blkTypeLevel}\tblkTypeNorm={s.blkTypeNorm}\tblkCeil={s.blkCeil}\t\
      wDiffType={s.wDiffType}\twDiffLocalInsts={s.wDiffLocalInsts}\twDiffFVarTypes={s.wDiffFVarTypes}\t\
      wDiffFVarValues={s.wDiffFVarValues}\twDiffDepth={s.wDiffDepth}\twDiffScoped={s.wDiffScoped}\t\
      wDiffLocalAttr={s.wDiffLocalAttr}\twDiffMaxSize={s.wDiffMaxSize}\twDiffCanon={s.wDiffCanon}\t\
      wDiffTransp={s.wDiffTransp}\twDiffExporting={s.wDiffExporting}\t\
      wSameAfterInst={s.wSameAfterInst}\twSameAfterInstHb={s.wSameAfterInstHb}\t\
      levelNormKeys={s.levelNormKeys}\tlevelNormMVars={s.levelNormMVars}\t\
      depRecov={s.depRecov}\tdepRecovHb={s.depRecovHb}\tdepRecovNs={s.depRecovNs}\t\
      depConflict={s.depConflict}\tdepNoNorm={s.depNoNorm}\t\
      depInstsKept={s.depInstsKept}\tdepInstsTotal={s.depInstsTotal}\t\
      wDiffTypeSkel={s.wDiffTypeSkel}\twDiffTypeOnly={s.wDiffTypeOnly}\twDiffCtxOnly={s.wDiffCtxOnly}\twDiffNothing={s.wDiffNothing}\t\
      wDiffTypeOnlyNs={s.wDiffTypeOnlyNs}\twDiffCtxOnlyNs={s.wDiffCtxOnlyNs}\t\
      missRespSeenFail={s.missRespSeenFail}\tmissRespSeenFailNs={s.missRespSeenFailNs}\t\
      hitRespSeen={s.hitRespSeen}\thitRespNew={s.hitRespNew}\t\
      missRespSeen={s.missRespSeen}\tmissRespNew={s.missRespNew}\t\
      hitRespSeenHb={s.hitRespSeenHb}\thitRespNewHb={s.hitRespNewHb}\t\
      missRespSeenHb={s.missRespSeenHb}\tmissRespNewHb={s.missRespNewHb}\t\
      hitRespSeenNs={s.hitRespSeenNs}\thitRespNewNs={s.hitRespNewNs}\t\
      missRespSeenNs={s.missRespSeenNs}\tmissRespNewNs={s.missRespNewNs}\t\
      blkFVarCtx={s.blkFVarCtx}\tblkFVarCtxHb={s.blkFVarCtxHb}\tblkConflate={s.blkConflate}\tblkInconsistent={s.blkInconsistent}\t\
      blkConflateHb={s.blkConflateHb}\tblkSkeleton={s.blkSkeleton}\tblkNormCtx={s.blkNormCtx}\t\
      blkNormCtxNoMV={s.blkNormCtxNoMV}\tblkNormCtxMVNoOut={s.blkNormCtxMVNoOut}\t\
      blkNormCtxMVOut={s.blkNormCtxMVOut}\tblkNone={s.blkNone}\t\
      blkLocalInstsHb={s.blkLocalInstsHb}\tblkDepthHb={s.blkDepthHb}\tblkScopedHb={s.blkScopedHb}\t\
      blkLocalAttrHb={s.blkLocalAttrHb}\tblkMaxSizeHb={s.blkMaxSizeHb}\tblkCanonHb={s.blkCanonHb}\t\
      blkExportingHb={s.blkExportingHb}\tblkLocalCtxHb={s.blkLocalCtxHb}\tblkTypeMVarHb={s.blkTypeMVarHb}\t\
      blkTypeLevelHb={s.blkTypeLevelHb}\tblkTypeNormHb={s.blkTypeNormHb}\tblkCeilHb={s.blkCeilHb}\t\
      blkSkeletonHb={s.blkSkeletonHb}\tblkNormCtxHb={s.blkNormCtxHb}\t\
      blkNormCtxHbNoMV={s.blkNormCtxHbNoMV}\tblkNormCtxHbMVNoOut={s.blkNormCtxHbMVNoOut}\t\
      blkNormCtxHbMVOut={s.blkNormCtxHbMVOut}\tblkNoneHb={s.blkNoneHb}"

/--
Returns the type class resolution cache entry for `key` from the transient
(`Meta.Cache.synthInstance`) or persistent (`synthInstanceCacheExt`) tier.
-/
private def findCachedResult? (key : SynthInstanceCacheKey) :
    MetaM (Option (SynthInstanceCacheEntry × Bool)) := do
  if let some entry := (← get).cache.synthInstance.find? key then
    return some (entry, false)
  let some ref := synthInstanceCacheExt.getState (← getEnv) | return none
  return (← ref.get).find? key |>.map (·, true)

/--
Inserts a result into the type class resolution cache: into the persistent tier if `persist` is
true, and otherwise into the transient `Meta.Cache.synthInstance` tier, which has the lifetime of
the current `Meta.State`.

Only context-free entries may be persisted: the key must not contain metavariables and the result
must be closed. Results with abstracted metavariables are only valid relative to the elaboration
context that created them: their degrees of freedom (e.g. universe metavariables not determined
by the key, cf. `Small`) are resolved by ambient constraints, so reusing them in a different
context can produce incorrectly instantiated terms.

Persistent insertions mutate the cache ref instead of the environment, so they survive
environment rollbacks; see `synthInstanceCacheExt`.
-/
private def recordInsertedKey (key : SynthInstanceCacheKey) (persist : Bool) : MetaM Unit := do
  if synthInstanceCacheStatsEnabled then
    let h := hash key
    if persist then synthKeyInsertedP.modify (·.insert h) else synthKeyInsertedT.modify (·.insert h)

private def insertCachedResult (key : SynthInstanceCacheKey) (entry : SynthInstanceCacheEntry)
    (persist : Bool) : MetaM Unit := do
  recordInsertedKey key persist
  if persist then
    recordSynthInstanceCacheStat fun s => { s with insertPersistent := s.insertPersistent + 1 }
    let some ref := synthInstanceCacheExt.getState (← getEnv) | return ()
    ref.modify (·.insert key entry)
  else
    recordSynthInstanceCacheStat fun s => { s with insertTransient := s.insertTransient + 1 }
    modifyCache fun c => { c with synthInstance := c.synthInstance.insert key entry }

/--
Whether the query determined every metavariable of an applied cache entry.

Reopening an entry mints a fresh metavariable for each one the value was abstracted over, and only
the `isDefEq` in `assignOutParams` can tie them back to the query. Unifying successfully is not
enough: a universe the query does not pin stays unassigned and leaks into the term (`declaration
contains universe level metavariables`, `stuck at solving universe constraint`). Such a value was a
degree of freedom of the elaboration that produced it, so the entry does not answer this query.
-/
private def queryDetermines (type : Expr) (result : Expr) : MetaM Bool := do
  let qLevels := (collectLevelMVars {} type).result
  for u in (collectLevelMVars {} result).result do
    unless qLevels.contains u do return false
  let qMVars := (type.collectMVars {}).result
  for m in (result.collectMVars {}).result do
    unless qMVars.contains m do return false
  return true

/--
Auxiliary function for converting a cached `AbstractMVarsResult` returned by `SynthInstance.main` into an `Expr`.
This function tries to avoid the potentially expensive `check` at `applyCachedAbstractResult?`.
-/
private def applyCachedAbstractResult? (type : Expr) (abstResult? : Option AbstractMVarsResult) :
    MetaM (Option (Option Expr)) := do
  let relaxedKey := synthLevelNorm || synthMVarNorm
  let some abstResult := abstResult? | return some none
  if abstResult.numMVars == 0 then
    /-
    Result does not introduce new metavariables, thus we don't need to perform (again)
    the `check` at `applyAbstractResult?`.
    This is an optimization.

    A value abstracted over the querying declaration's universe metavariables carries them as
    parameters; instantiating them with fresh metavariables keeps this path available, and the
    `isDefEq` in `assignOutParams` assigns them from the actual query.
    -/
    let e ← if abstResult.paramNames.isEmpty then
        pure abstResult.expr
      else
        let us ← abstResult.paramNames.mapM fun _ => mkFreshLevelMVar
        pure (abstResult.expr.instantiateLevelParamsArray abstResult.paramNames us)
    /-
    With the exact key, an entry that fails to unify is the designed outcome: an
    `.mvarsOutputParams` key wildcards the output parameters, so entries deliberately over-share and
    `assignOutParams` is what reports "this instance's output parameters are not the ones you want".
    Only a *normalized* key can produce an entry that does not answer the query at all, and there the
    failure to apply must not be reported as the absence of an instance (a completeness bug): the
    search has to run.
    -/
    unless (← assignOutParams type e) do
      return if relaxedKey then none else some none
    let e ← instantiateMVars e
    if relaxedKey then
      unless (← queryDetermines type e) do return none
    return some (some e)
  else
    let (_, _, result) ← openAbstractMVarsResult abstResult
    unless (← assignOutParams type result) do
      return if relaxedKey then none else some none
    let result ← instantiateMVars result
    if relaxedKey then
      unless (← queryDetermines type result) do return none
    check result
    return some (some result)

/--
Abstracts the metavariables a cached value still mentions, on top of the abstraction the search
already performed one depth down. Binders introduced here wrap the existing ones, so both counts are
kept in `mvars` and both universe parameter sets in `paramNames`.
-/
private def abstractRemaining (queryMVars : Array MVarId) (r : AbstractMVarsResult) :
    MetaM (Option AbstractMVarsResult) := do
  unless r.expr.hasMVar do return some r
  let e ← instantiateMVars r.expr
  for m in (e.collectMVars {}).result do
    -- On a hit, `openAbstractMVarsResult` mints a fresh metavariable for each abstracted one, and
    -- the only thing that can re-determine it is the `isDefEq` in `assignOutParams`, which unifies
    -- the query with the result's type. A metavariable of the value that the query does not mention
    -- is a degree of freedom of the elaboration that created it: re-minting it for another query
    -- would leave it unconstrained, so the value must not be reused. This mirrors the universe case
    -- in `abstractResultLevels` and the free-variable case in `abstractOverClosure?`.
    unless queryMVars.contains m do return none
  -- `levels := false`: universes are handled by `abstractResultLevels`, which refuses the ones the
  -- query does not determine. Letting `abstractMVars` abstract them here would bypass that check,
  -- and that was what still broke `QPF/Univariate/Basic`.
  let r2 ← abstractMVars e (levels := false)
  return some { paramNames := r.paramNames ++ r2.paramNames
                mvars      := r.mvars ++ r2.mvars
                expr       := r2.expr }

/--
Abstracts the universe metavariables still mentioned by a cached value into universe parameters.

`abstractMVars` leaves universe metavariables from lower metavariable-context depths alone (it treats
them as constants), so the value produced for a query keeps the *querying declaration's* universe
metavariables. That is invisible while their identity is also part of the key, but the key
canonicalizes them (`canonKeyLevels`), so the value must not mention them either: it would be
reopened in a declaration whose metavariable context does not have them. `openAbstractMVarsResult`
mints a fresh universe metavariable per parameter on every use, and the `isDefEq` in
`assignOutParams` unifies them against the actual query.
-/
private def abstractResultLevels (queryLevelMVars : Array LMVarId) (r : AbstractMVarsResult) :
    MetaM (Option AbstractMVarsResult) := do
  unless r.expr.hasLevelMVar do return some r
  let e ← instantiateMVars r.expr
  let st := collectLevelMVars {} e
  if st.result.isEmpty then
    return some { r with expr := e }
  let mut names := r.paramNames
  let mut m : Std.HashMap LMVarId Level := {}
  for id in st.result do
    -- On a hit the only thing that re-determines a universe is the `isDefEq` in `assignOutParams`,
    -- which unifies the *query type* with the result's type. A universe metavariable the query type
    -- does not mention is therefore a degree of freedom of the elaboration that created the value,
    -- resolved by ambient constraints (`Small` is the standard example); re-minting it for another
    -- query would leave it unconstrained, so such a value must not be reused. See
    -- `insertCachedResult`.
    unless queryLevelMVars.contains id do return none
    let n := Name.mkNum `_snu names.size
    names := names.push n
    m := m.insert id (mkLevelParam n)
  let f? : Level → Option Level := fun
    | .mvar id => m[id]?
    | _        => none
  return some { r with paramNames := names, expr := e.replaceLevel f? }

/-- Helper function for caching synthesized type class instances. -/
private def cacheResult (cacheKey : SynthInstanceCacheKey) (relSynthPendingDepth : Option Nat)
    (kind : PreprocessKind) (normalized : Bool) (abstResult? : Option AbstractMVarsResult)
    (result? : Option Expr) (queryLevelMVars : Array LMVarId := #[])
    (queryMVars : Array MVarId := #[]) : MetaM Unit := do
  -- The stored value: for a closed result we store the concrete `result` expr with an empty
  -- `AbstractMVarsResult` so that `applyCachedAbstractResult?` can skip re-`check`ing it.
  -- `none` here means the value cannot be reused at all and nothing is cached.
  let value?? : Option (Option AbstractMVarsResult) ←
    match abstResult? with
    | none => pure (some none)
    | some abstResult =>
      let raw : Option AbstractMVarsResult :=
        if abstResult.numMVars == 0 && abstResult.paramNames.isEmpty && kind matches .noMVars | .mvarsNoOutputParams then
          result?.map fun result => { expr := result, paramNames := #[], mvars := #[] }
        else
          some abstResult
      match raw with
      | none   => pure (some none)
      | some r =>
        if !synthLevelNorm then
          pure (some (some r))
        else
          -- Re-abstract at the *caller's* depth: the `abstractMVars` inside the search ran one depth
          -- down, where the querying declaration's own metavariables count as constants and stay in
          -- the term, and the key no longer distinguishes them.
          match ← abstractRemaining queryMVars r with
          | none   => pure none
          | some r =>
            match ← abstractResultLevels queryLevelMVars r with
            | none   => pure none
            | some v => pure (some (some v))
  let some value? := value?? | return ()
  -- Only context-free entries may be persisted: a key without metavariables, a key that does not
  -- depend on the identity of any free variable, and a closed value (no abstracted metavariables,
  -- no free variables); see `insertCachedResult`.
  --
  -- The key is tested for metavariables directly rather than through `.noMVars`. An
  -- `.mvarsOutputParams` query has its output parameters replaced by a wildcard in the key, so the
  -- key is metavariable-free whenever every metavariable sits in an output parameter, even though
  -- the query itself is not. Such an entry is as context-free as a `.noMVars` one: the wildcard
  -- stands for a value the input parameters determine, and a hit re-derives it by unifying the
  -- cached result against the query (`assignOutParams`).
  --
  -- A `normalized` key names its free variables by canonical position and records their types in
  -- `normFVarTypes`, so it is context-free even though it mentions free variables. A raw key is
  -- context-free only if it mentions none: an `FVarId` identifies a variable only within the
  -- `NameGenerator` that created it, and the cache outlives any of them.
  let persist := !cacheKey.type.hasMVar &&
    (normalized || (cacheKey.localInsts.isEmpty && !cacheKey.type.hasFVar)) &&
    (value?.all fun r => r.numMVars == 0 && (synthLevelNorm || r.paramNames.isEmpty) && !r.expr.hasFVar) &&
    (← IO.getEnv "LEAN_NO_PERSIST") != some "1"
  recordSynthInstanceCacheStat fun s =>
    let s := match kind with
      | .noMVars             => { s with cachedNoMVars := s.cachedNoMVars + 1 }
      | .mvarsNoOutputParams => { s with cachedMVarsNoOut := s.cachedMVarsNoOut + 1 }
      | .mvarsOutputParams   => { s with cachedMVarsOut := s.cachedMVarsOut + 1 }
    if result?.isSome then { s with cachedFound := s.cachedFound + 1 }
    else { s with cachedFailed := s.cachedFailed + 1 }
  insertCachedResult cacheKey { relSynthPendingDepth, result := value? } (persist := persist)
  recordBlankedKey cacheKey

/-!
Free-variable normalization of the cache key and result. Two `.noMVars` queries that are
structurally identical up to the identities of their free variables (e.g. `Foo α` under `[Foo α]`
vs. `Foo β` under `[Foo β]`) are made to share a single cache entry: every free variable reachable
from the query type and the local instances is renamed to a canonical positional identifier, and
the result is stored over the same canonical variables and re-instantiated with the current
context's free variables on a hit.

This is sound because a hit means the normalized key components are `BEq`-equal, i.e. the two
contexts are identical up to free-variable renaming, and the synthesized result only mentions free
variables in that closure (the query's variables and the local instances). Queries that cannot be
soundly normalized fall back to the raw (unnormalized) key: see `normalizeContext?`.
-/
namespace SynthNorm

/-- Canonical positional free-variable identifier used in the normalized cache key. -/
private def canonFVarId (i : Nat) : FVarId := ⟨.mkNum `_snf i⟩

/-- Canonical positional identifier for an assignable metavariable of the key. The key is only ever
compared, never elaborated, so a metavariable may be represented by a marker free variable. -/
private def canonMVarId (i : Nat) : FVarId := ⟨.mkNum `_snm i⟩

private structure State where
  /-- Assigns each source free variable its canonical position. Persistent, so that a memoized
  closure seeds a query's state in constant time. -/
  fmap  : PersistentHashMap FVarId Nat := {}
  /-- Canonical position to source free variable (inverse of `fmap`), for re-instantiation. -/
  order : Array FVarId := #[]
  /-- Canonical position to the (recursively normalized) type of that free variable. -/
  types : Array Expr := #[]
  /-- Canonical position to the normalized value of that free variable, if it is let-bound. -/
  values : Array (Option Expr) := #[]
  /-- Set when the closure cannot be soundly normalized (let-bound or mvar-typed variable). -/
  bail  : Bool := false
  /-- Closure variables whose raw `LocalDecl` type or let-value mentions a metavariable, with the
  instantiation used; see `SynthNormClosureMemo.mvarTyped`. -/
  mvarTyped : Array (FVarId × Bool × Expr) := #[]
  /-- Why `bail` was set: 1 not in the local context, 3 mvar-typed. Statistics only. -/
  bailReason : Nat := 0
  /-- Canonical position of each expression metavariable, assigned by first occurrence. -/
  mmap : PersistentHashMap MVarId Nat := {}
  /-- Number of entries in `mmap`. -/
  nmvars : Nat := 0
  /--
  Memoizes `normExpr` on visited subterms so that terms with DAG sharing are traversed in DAG
  size, not tree size. Sound because positions are assigned by first occurrence and never change:
  revisiting a subterm yields the same normalization. Keyed structurally (`ExprStructEq` hashes
  are cached and its equality short-circuits on pointer identity).
  -/
  cache : Std.HashMap ExprStructEq Expr := {}

private abbrev M := ReaderT LocalContext (StateT State MetaM)

/--
Renames every free variable to a canonical positional identifier by first-occurrence order,
recording and recursively normalizing each one's type, and its value if it is let-bound. Sets
`bail` on a variable whose type or value contains an unassigned metavariable, which is not
context-free and so cannot be soundly normalized.
-/
private partial def normExpr (e : Expr) : M Expr := do
  if (← get).bail then return e
  unless e.hasFVar || (synthMVarNorm && e.hasMVar) do return e
  match e with
  | .mvar mvarId =>
    -- An *assignable* metavariable is a hole the search may solve, and the cached result is
    -- re-unified against the actual query on every use (`assignOutParams`), so its identity does not
    -- belong in the key. An unassignable one behaves as a constant and must be kept, exactly as
    -- `mkTableKey` treats it.
    if !synthMVarNorm then return e
    if let some i := (← get).mmap.find? mvarId then
      return .fvar (canonMVarId i)
    unless ← mvarId.isAssignable do return e
    let i := (← get).nmvars
    modify fun s => { s with mmap := s.mmap.insert mvarId i, nmvars := i + 1 }
    return .fvar (canonMVarId i)
  | .fvar id =>
    if let some i := (← get).fmap.find? id then
      return .fvar (canonFVarId i)
    -- `preprocess` puts this marker in output-parameter positions; it is a constant, not a
    -- variable of the local context, and must not be renamed (nor bail the normalization).
    if id.name == `__wild__ then return e
    match (← read).find? id with
    | none =>
      modify fun s => { s with bail := true, bailReason := 1 }
      return e
    | some decl =>
      -- `Expr.hasMVar` is a syntactic flag: it stays set for metavariables that are already
      -- assigned, whose values are context-free. Instantiate before deciding to bail. The result is
      -- recorded even when we bail below: assigning the metavariable that made us bail must
      -- invalidate the memoized closure.
      let inst (isValue : Bool) (e : Expr) : M Expr := do
        unless e.hasMVar do return e
        let e ← instantiateMVars e
        modify fun s => { s with mvarTyped := s.mvarTyped.push (id, isValue, e) }
        return e
      let type ← inst false decl.type
      -- A nondependent `ldecl` (`have`) hides its value from definitional unfolding, so
      -- `LocalDecl.value?` reports none and the value stays out of the key.
      let value? ← match decl.value? with
        | none   => pure none
        | some v => do
          let v ← inst true v
          pure (some v)
      if !synthMVarNorm && (type.hasMVar || (match value? with | some v => v.hasMVar | none => false)) then
        modify fun s => { s with bail := true, bailReason := 3 }
        return e
      let i := (← get).order.size
      modify fun s =>
        { s with fmap := s.fmap.insert id i, order := s.order.push id,
                 types := s.types.push default, values := s.values.push none }
      let nty ← normExpr type
      let nval? ← match value? with
        | none   => pure none
        | some v => do
          let v ← normExpr v
          pure (some v)
      modify fun s => { s with types := s.types.set! i nty, values := s.values.set! i nval? }
      return .fvar (canonFVarId i)
  | _ =>
    if let some r := (← get).cache[(e : ExprStructEq)]? then
      return r
    let r ← match e with
      | .app f a          => pure <| .app (← normExpr f) (← normExpr a)
      | .lam n d b bi     => pure <| .lam n (← normExpr d) (← normExpr b) bi
      | .forallE n d b bi => pure <| .forallE n (← normExpr d) (← normExpr b) bi
      | .letE n t v b nd  => pure <| .letE n (← normExpr t) (← normExpr v) (← normExpr b) nd
      | .mdata m b        => pure <| .mdata m (← normExpr b)
      | .proj s i b       => pure <| .proj s i (← normExpr b)
      | e                 => pure e
    modify fun s => { s with cache := s.cache.insert e r }
    return r

/-- The free-variable-normalized cache context for a query; see `normalizeContext?`. -/
structure Context where
  normType        : Expr
  canonLocalInsts : LocalInstances
  fvarTypes       : Array Expr
  fvarValues      : Array (Option Expr)
  fmap            : PersistentHashMap FVarId Nat
  order           : Array FVarId

private def recordBail (reason : Nat) : MetaM Unit :=
  recordSynthInstanceCacheStat fun s => match reason with
    | 1 => { s with bailNotFound := s.bailNotFound + 1 }
    | _ => { s with bailMVarType := s.bailMVarType + 1 }

/--
Whether a memoized closure is still valid: every closure variable whose type mentions a
metavariable must still instantiate to what the closure was built from. The other closure
variables have immutable types, and the local instances are compared by the caller.
-/
private def isValidMemo (lctx : LocalContext) (memo : SynthNormClosureMemo) : MetaM Bool := do
  for (id, isValue, e) in memo.mvarTyped do
    let some decl := lctx.find? id | return false
    let some raw := (if isValue then decl.value? else some decl.type) | return false
    unless (← instantiateMVars raw) == e do return false
  return true

/--
The free-variable-normalized closure of the local instances, or `none` if it cannot be soundly
normalized. Memoized in `Meta.Cache.synthNormClosure`: the closure is the same for every query made
under the same local instances, and normalizing it per query dominates the cost of a cache key.
-/
private def getClosure? (localInsts : LocalInstances) : MetaM (Option SynthNormClosure) := do
  let lctx ← getLCtx
  let cache := (← get).cache
  if let some memo := cache.synthNormClosure then
    if memo.localInsts == localInsts && (← isValidMemo lctx memo) then
      recordSynthInstanceCacheStat fun s => { s with normMemoHits := s.normMemoHits + 1 }
      return memo.closure?
  let go : M LocalInstances :=
    localInsts.mapM fun li => return { li with fvar := ← normExpr li.fvar }
  let (canonLocalInsts, st) ← go.run lctx |>.run {}
  if st.bail then recordBail st.bailReason
  let closure? :=
    if st.bail then none
    else some { fmap := st.fmap, order := st.order, types := st.types, values := st.values,
                canonLocalInsts }
  modifyCache fun c =>
    { c with synthNormClosure := some { localInsts, mvarTyped := st.mvarTyped, closure? } }
  recordSynthInstanceCacheStat fun s =>
    { s with normMemoBuilds := s.normMemoBuilds + 1,
             normClosureSize := s.normClosureSize + st.order.size,
             normLocalInsts := s.normLocalInsts + localInsts.size,
             normMVarTypedDecls := s.normMVarTypedDecls + st.mvarTyped.size }
  return closure?

/--
Computes the free-variable-normalized cache context for a `.noMVars` query, or `none` if it cannot
be soundly normalized (some free variable in the closure has an unassigned metavariable in its type
or value). The closure comprises the free variables of the local instances and of `cacheKeyType`,
together with their types, transitively. The local instances are normalized first, so that their
part of the closure does not depend on the query and can be memoized; see `getClosure?`.
-/
def normalizeContext? (cacheKeyType : Expr) (localInsts : LocalInstances) :
    MetaM (Option Context) := do
  let hb0 ← if synthInstanceCacheStatsEnabled then IO.getNumHeartbeats else pure 0
  let r? ← go cacheKeyType localInsts
  if synthInstanceCacheStatsEnabled then
    let d := (← IO.getNumHeartbeats) - hb0
    recordSynthInstanceCacheStat fun s =>
      { s with normCalls := s.normCalls + 1, normHb := s.normHb + d }
  return r?
where
  go (cacheKeyType : Expr) (localInsts : LocalInstances) : MetaM (Option Context) := do
    let some closure ← getClosure? localInsts | return none
    let lctx ← getLCtx
    -- Seed from the memoized closure; the query type may extend it with further free variables.
    let st0 : State := { fmap := closure.fmap, order := closure.order, types := closure.types,
                         values := closure.values }
    let (normType, st) ← (normExpr cacheKeyType).run lctx |>.run st0
    if st.bail then
      recordBail st.bailReason
      return none
    return some { normType, canonLocalInsts := closure.canonLocalInsts, fvarTypes := st.types,
                  fvarValues := st.values, fmap := st.fmap, order := st.order }

/--
Abstracts the closure free variables of `e` into loose bound variables (positional, by the closure
`order`), or `none` if `e` mentions a free variable outside the closure (in which case the value is
context-dependent beyond its key and must not be reused).

The abstracted value contains no context-specific free variables, so it is safe to store in the
shared cache and re-instantiate in a different context (cf. `reopen`), analogously to how
`abstractMVars` produces a closed schema. `.noMVars` results have no abstracted metavariables, so
`e` never wraps the value in metavariable binders and this abstraction composes with the universe
handling in `openAbstractMVarsResult`.
-/
def abstractOverClosure? (ctx : Context) (e : Expr) : Option Expr :=
  -- Abstract first, then check the (cached) `hasFVar` flag of the result: any remaining free
  -- variable is outside the closure. Unlike `hasAnyFVar`, this is linear in the DAG size of `e`.
  let e := e.abstract (ctx.order.map Expr.fvar)
  if e.hasFVar then none else some e

/-- Abstracts the free variables of a cache value, or `none` if the result escapes the closure. -/
def abstractValue? (ctx : Context) (abstResult? : Option AbstractMVarsResult) (result? : Option Expr) :
    Option (Option AbstractMVarsResult × Option Expr) := do
  let abstResult? ← match abstResult? with
    | none   => some none
    | some a => (abstractOverClosure? ctx a.expr).map fun e => some { a with expr := e }
  let result? ← match result? with
    | none   => some none
    | some r => (abstractOverClosure? ctx r).map some
  some (abstResult?, result?)

/--
Re-instantiates a closure-abstracted value (see `abstractOverClosure?`) with the current context's
closure free variables `order`.
-/
def reopen (order : Array FVarId) (e : Expr) : Expr :=
  e.instantiateRev (order.map Expr.fvar)

end SynthNorm

/--
Computes the fingerprint under which it is sound to memoize that the query `key` got stuck
(`isDefEqStuck`), or `none` if memoizing it is unsound. A stuck query whose key is unchanged can
still succeed when re-run if the search outcome depends on state outside the key:
- Local instances participate in the key only by their `FVarId`. If a local instance's type
  contains a metavariable, assigning it later un-sticks the query without changing the key.
- Non-natural metavariables in the query can be resolved by the search itself as a side effect
  (`synthPending`), and delayed assignments can make progress, both without a prior key change.
- Level metavariables at the caller's metavariable-context depth may be assigned during the
  search (`allowLevelAssignments`), so stuckness additionally depends on their current
  assignability. This set is the returned fingerprint; it must be compared at lookup time.
-/
private def stuckMemoFingerprint? (key : SynthInstanceCacheKey) : MetaM (Option (Array LMVarId)) := do
  for localInst in key.localInsts do
    if (← instantiateMVars (← localInst.fvar.fvarId!.getDecl).type).hasMVar then
      return none
  let type ← instantiateMVars key.type
  for mvarId in (type.collectMVars {}).result do
    unless (← mvarId.getDecl).kind.isNatural do
      return none
    if (← mvarId.isDelayedAssigned) then
      return none
  let assignable ← (collectLevelMVars {} type).result.filterM isLevelMVarAssignable
  return some <| assignable.insertionSort fun u v => u.name.quickLt v.name

/--
Records a completed lookup: whether it was served from the cache, and whether the response it
produced had already been produced. The response is canonicalized so that the same instance
synthesized in different local contexts counts as the same response; a failure is its own response.
-/
private def recordLookupOutcome (key rawKey : SynthInstanceCacheKey) (entryHash : UInt64)
    (isHit : Bool) (result? : Option Expr) (t0 hb0 : Nat) (depParent : Std.HashSet Name)
    (mctx0 : MetavarContext) : MetaM Unit := do
  if synthTraceAll then
    -- `rawKey.type` is the preprocessed query, the same in both runs; the normalized `key` is not.
    let r : String ← match result? with
      | none   => pure "FAIL"
      | some e => do
        -- The *type* of the result, not the key: the key wildcards output parameters, which is
        -- precisely what `assignOutParams` decides from the entry.
        let ty ← instantiateMVars (← inferType e)
        pure s!"{← instantiateMVars e}  :  {ty}"
    IO.eprintln s!"SYNTH\t{if isHit then "hit " else "miss"}\t{← instantiateMVars rawKey.type}\t=>\t{r}"
  if synthInstanceCacheStatsEnabled then
    let dt := (← IO.monoNanosNow) - t0
    let dhb := (← IO.getNumHeartbeats) - hb0
    let fp ← match result? with
      -- A failure is a response *to this query*: fingerprint it by the key, so that two different
      -- queries that both fail do not count as the same response.
      | none   => pure (mixHash 1 (hash (StatsNorm.run true true true key.type)))
      | some e => do
        let e ← instantiateMVars e
        -- A successful search very often returns a bare local-instance free variable, which carries
        -- no structure of its own: canonicalizing its variables away would collapse every "the answer
        -- is some local instance" result into a single response. Fingerprint it with its type.
        let t ← instantiateMVars (← inferType e)
        pure (mixHash 2 (mixHash (hash (StatsNorm.run true true true e))
                                 (hash (StatsNorm.run true true true t))))
    let seen := (← synthResponseSeen.get).contains fp
    let prevKey? := (← synthResponseKey.get)[fp]?
    synthResponseSeen.modify (·.insert fp)
    unless seen do synthResponseKey.modify (·.insert fp key)
    /-
    Dependency-validated key: keep only the local instances whose class the search was actually
    consulted for. `getInstances` offers a local instance as a candidate only for a goal whose class
    name matches it exactly, so local instances of classes that never came up cannot have changed the
    search. A cache hit does not re-run `getInstances`, so it inherits the dependencies recorded when
    its entry was first computed; either way the set is folded into the enclosing query, whose replay
    depends on this one.
    -/
    let mut deps ← synthDepCur.get
    if isHit then
      for c in (← synthDepOfKey.get)[entryHash]?.getD {} do deps := deps.insert c
    else
      synthDepOfKey.modify (·.insert entryHash deps)
    let mut merged := depParent
    for c in deps do merged := merged.insert c
    synthDepCur.set merged
    unless isHit || !synthDepEnabled do
      let kept := rawKey.localInsts.filter fun li => deps.contains li.className
      recordSynthInstanceCacheStat fun s =>
        { s with depInstsKept := s.depInstsKept + kept.size,
                 depInstsTotal := s.depInstsTotal + rawKey.localInsts.size }
      -- Class order across local instances does not affect any candidate list, so canonicalize it;
      -- the (stable) order within a class does, and is preserved.
      let kept := kept.insertionSort fun a b => a.className.quickLt b.className
      -- Renormalize as the lookup would have, i.e. in the pre-search metavariable context.
      match ← withMCtx mctx0 (SynthNorm.normalizeContext? rawKey.type kept) with
      | none => recordSynthInstanceCacheStat fun s => { s with depNoNorm := s.depNoNorm + 1 }
      | some c =>
        let depKey : SynthInstanceCacheKey := { rawKey with
          localInsts := c.canonLocalInsts, type := c.normType,
          normFVarTypes := c.fvarTypes, normFVarValues := c.fvarValues }
        let dkh := hash depKey
        match (← synthDepKeyResp.get)[dkh]? with
        | none => synthDepKeyResp.modify (·.insert dkh fp)
        | some fp0 =>
          if fp0 == fp then
            recordSynthInstanceCacheStat fun s =>
              { s with depRecov := s.depRecov + 1, depRecovHb := s.depRecovHb + dhb,
                       depRecovNs := s.depRecovNs + dt }
          else
            recordSynthInstanceCacheStat fun s => { s with depConflict := s.depConflict + 1 }
    if let some k0 := prevKey? then
      if !isHit && seen then
        -- Did the earlier query only *look* different because its metavariables were still open?
        let a := StatsNorm.run true true true k0.type
        let b := StatsNorm.run true true true key.type
        if a != b then
          pure ()
    if let some k0 := prevKey? then
      if !isHit && seen && synthDumpCtx then
        -- Structurally identical query (context-independent normalization agrees) that still missed:
        -- show what the two contexts actually disagree about.
        if StatsNorm.run true true true k0.type == StatsNorm.run true true true key.type then
          let f (b : Bool) (n : String) : String := if b then n ++ "." else ""
          let flags :=
            f (k0.type != key.type) "T" ++ f (k0.localInsts != key.localInsts) "LI" ++
            f (k0.normFVarTypes != key.normFVarTypes) "FT" ++
            f (k0.normFVarValues != key.normFVarValues) "FV" ++
            f (k0.activeScopedInsts != key.activeScopedInsts) "SC" ++
            f (k0.localAttrInsts != key.localAttrInsts) "LA" ++
            f (k0.isExporting != key.isExporting) "EX" ++
            f (k0.synthPendingDepth != key.synthPendingDepth) "DE"
          IO.eprintln s!"CTXDIFF\t{flags}\t{k0.normFVarTypes.size}\t{key.normFVarTypes.size}\t\
            {k0.type}\t{key.type}\t\
            {k0.localInsts.map (·.className)}\t{key.localInsts.map (·.className)}"
    if let some k0 := prevKey? then
      if !isHit && seen && synthDumpSame then
        if StatsNorm.run true true true k0.type != StatsNorm.run true true true key.type then
          IO.eprintln s!"SAMEANS\n  q1= {k0.type}\n  q2= {key.type}\n  ans={result?}\n"
    recordSynthInstanceCacheStat fun s =>
      match isHit, seen with
      | true,  true  => { s with hitRespSeen := s.hitRespSeen + 1, hitRespSeenHb := s.hitRespSeenHb + dhb, hitRespSeenNs := s.hitRespSeenNs + dt }
      | true,  false => { s with hitRespNew := s.hitRespNew + 1, hitRespNewHb := s.hitRespNewHb + dhb, hitRespNewNs := s.hitRespNewNs + dt }
      | false, true  =>
        let s := { s with missRespSeen := s.missRespSeen + 1, missRespSeenHb := s.missRespSeenHb + dhb, missRespSeenNs := s.missRespSeenNs + dt }
        let s := if result?.isNone then
            { s with missRespSeenFail := s.missRespSeenFail + 1, missRespSeenFailNs := s.missRespSeenFailNs + dt }
          else s
        match prevKey? with
        | none => s
        | some k0 =>
          let dTy := k0.type != key.type
          let dLI := k0.localInsts != key.localInsts
          let dFT := k0.normFVarTypes != key.normFVarTypes
          let dFV := k0.normFVarValues != key.normFVarValues
          let dDe := k0.synthPendingDepth != key.synthPendingDepth
          let dSc := k0.activeScopedInsts != key.activeScopedInsts
          let dLA := k0.localAttrInsts != key.localAttrInsts
          let dMS := k0.maxResultSize != key.maxResultSize
          let dCa := k0.canonInstances != key.canonInstances
          let dTr := k0.respectTransparency != key.respectTransparency
                     || k0.respectTransparencyTypes != key.respectTransparencyTypes
          let dEx := k0.isExporting != key.isExporting
          let anyCtx := dLI || dFT || dFV || dDe || dSc || dLA || dMS || dCa || dTr || dEx
          let s := if dTy then { s with wDiffType := s.wDiffType + 1 } else s
          let s := if dTy && StatsNorm.run true true true k0.type != StatsNorm.run true true true key.type then
              { s with wDiffTypeSkel := s.wDiffTypeSkel + 1 } else s
          let s := if dLI then { s with wDiffLocalInsts := s.wDiffLocalInsts + 1 } else s
          let s := if dFT then { s with wDiffFVarTypes := s.wDiffFVarTypes + 1 } else s
          let s := if dFV then { s with wDiffFVarValues := s.wDiffFVarValues + 1 } else s
          let s := if dDe then { s with wDiffDepth := s.wDiffDepth + 1 } else s
          let s := if dSc then { s with wDiffScoped := s.wDiffScoped + 1 } else s
          let s := if dLA then { s with wDiffLocalAttr := s.wDiffLocalAttr + 1 } else s
          let s := if dMS then { s with wDiffMaxSize := s.wDiffMaxSize + 1 } else s
          let s := if dCa then { s with wDiffCanon := s.wDiffCanon + 1 } else s
          let s := if dTr then { s with wDiffTransp := s.wDiffTransp + 1 } else s
          let s := if dEx then { s with wDiffExporting := s.wDiffExporting + 1 } else s
          if dTy && !anyCtx then { s with wDiffTypeOnly := s.wDiffTypeOnly + 1, wDiffTypeOnlyNs := s.wDiffTypeOnlyNs + dt }
          else if !dTy && anyCtx then { s with wDiffCtxOnly := s.wDiffCtxOnly + 1, wDiffCtxOnlyNs := s.wDiffCtxOnlyNs + dt }
          else if !dTy && !anyCtx then { s with wDiffNothing := s.wDiffNothing + 1 }
          else s
      | false, false => { s with missRespNew := s.missRespNew + 1, missRespNewHb := s.missRespNewHb + dhb, missRespNewNs := s.missRespNewNs + dt }

/--
Canonicalizes the universe metavariables of a cache key by first occurrence, so that the same query
issued in different declarations, each minting a fresh `?u`, shares one entry. `preprocess` already
does this for output universe parameters; a query whose only metavariables are universes is
classified `.noMVars` (`Expr.hasMVar` does not see them) and never reaches that code.
-/
def canonKeyLevels (key : SynthInstanceCacheKey) : SynthInstanceCacheKey × Array LMVarId := Id.run do
  let mut st : CollectLevelMVars.State := {}
  if key.type.hasLevelMVar then
    st := collectLevelMVars st key.type
  for t in key.normFVarTypes do
    if t.hasLevelMVar then
      st := collectLevelMVars st t
  for v? in key.normFVarValues do
    if let some v := v? then
      if v.hasLevelMVar then
        st := collectLevelMVars st v
  if st.result.isEmpty then
    return (key, #[])
  let mut m : Std.HashMap LMVarId Level := {}
  let mut i := 0
  for id in st.result do
    m := m.insert id (mkLevelParam (.mkNum `_snu i))
    i := i + 1
  let f? : Level → Option Level := fun
    | .mvar id => m[id]?
    | _        => none
  -- `Expr.replaceLevel` allocates a fresh cache of `ReplaceLevelImpl.cacheSize` entries on every
  -- call, so rewrite every component of the key in a single traversal rather than one per component.
  let placeholder := mkSort .zero
  let n := key.normFVarTypes.size
  let args := #[key.type] ++ key.normFVarTypes
    ++ key.normFVarValues.map (·.getD placeholder)
  let bundle := (mkAppN (mkConst `_snu) args).replaceLevel f?
  let args := bundle.getAppArgs
  return ({ key with
    type := args[0]!,
    normFVarTypes := args.extract 1 (1 + n),
    normFVarValues := key.normFVarValues.mapIdx fun i v? => v?.map fun _ => args[1 + n + i]! },
    st.result)

def synthInstanceCore? (type : Expr) (maxResultSize? : Option Nat := none) : MetaM (Option Expr) := do
  let lookupT0 ← if synthInstanceCacheStatsEnabled then IO.monoNanosNow else pure 0
  let lookupHb0 ← if synthInstanceCacheStatsEnabled then IO.getNumHeartbeats else pure 0
  let lookupMCtx ← if synthInstanceCacheStatsEnabled then getMCtx else pure {}
  let depParent ← if synthInstanceCacheStatsEnabled then
      let p ← synthDepCur.get
      synthDepCur.set {}
      pure p
    else pure {}
  let opts ← getOptions
  let maxResultSize := maxResultSize?.getD (synthInstance.maxSize.get opts)
  withTraceNode `Meta.synthInstance
    (fun _ => return m!"{← instantiateMVars type}") do
  withConfig (fun config => { config with isDefEqStuckEx := true, transparency := TransparencyMode.instances,
                                          foApprox := true, ctxApprox := true, constApprox := false, univApprox := false }) do
  withInTypeClassResolution do
    let localInsts ← getLocalInstances
    let type ← instantiateMVars type
    let { type, cacheKeyType, kind } ← preprocess type
    -- Normalize the free variables of the key and result so that structurally identical queries in
    -- different local contexts share a cache entry. Metavariables are left exactly as they are, so
    -- this applies to metavariable-laden queries as well: their keys are otherwise context-specific
    -- and can never be shared. `.mvarsOutputParams` keys have their output parameters replaced by a
    -- wildcard already, so they are usually metavariable-free apart from it.
    let normCtx? ← SynthNorm.normalizeContext? cacheKeyType localInsts
    if normCtx?.isNone then
      recordSynthInstanceCacheStat fun s => { s with normBail := s.normBail + 1 }
    let synthPendingDepth := (← read).synthPendingDepth
    let depthSuffix : MessageData :=
      if synthPendingDepth == 0 then m!"" else m!" (synthPendingDepth := {synthPendingDepth})"
    -- Fold `synthPending` activity into the enclosing query's accumulator, if any.
    let foldActivity (activity : SynthPendingActivity) : MetaM Unit := do
      if activity.maxDepth.isSome || activity.guardHit then
        if let some ref := (← read).synthPendingActivityRef? then
          ref.modify fun a => {
            maxDepth := match a.maxDepth, activity.maxDepth with
              | some d₁, some d₂ => some (d₁.max d₂)
              | some d, none | none, some d => some d
              | none, none => none
            guardHit := a.guardHit || activity.guardHit }
    -- Base cache key: context fields for cross-command persistence plus the fvar-normalized
    -- components. `synthPendingDepth` is `none` for the depth-shared entry and `some depth` for
    -- the depth-exact one (see `SynthInstanceCacheKey.synthPendingDepth`).
    let rawBaseKey : SynthInstanceCacheKey :=
      { localInsts, type := cacheKeyType, synthPendingDepth := none,
        activeScopedInsts := instanceExtension.getActiveScopesWithEntries (← getEnv),
        localAttrInsts := instanceExtension.getState (← getEnv) |>.localInstanceNames,
        maxResultSize,
        canonInstances := backward.synthInstance.canonInstances.get opts,
        -- read by name: importing `Lean.Meta.ExprDefEq` here would be a cycle
        respectTransparency := opts.getBool `backward.isDefEq.respectTransparency true,
        respectTransparencyTypes := opts.getBool `backward.isDefEq.respectTransparency.types true,
        isExporting := (← getEnv).isExporting }
    let baseKey := match normCtx? with
      | some c => { rawBaseKey with localInsts := c.canonLocalInsts, type := c.normType, normFVarTypes := c.fvarTypes, normFVarValues := c.fvarValues }
      | none   => rawBaseKey
    let nLevelMVars := (collectLevelMVars {} baseKey.type).result.size
    recordSynthInstanceCacheStat fun s =>
      if nLevelMVars > 0 then
        { s with levelNormKeys := s.levelNormKeys + 1, levelNormMVars := s.levelNormMVars + nLevelMVars }
      else s
    -- What `assignOutParams` can re-determine on a hit is exactly what the query mentions: it
    -- unifies `type` with the result's type. Anything else in a value is a degree of freedom of the
    -- elaboration that produced it and makes the value unshareable.
    let queryLevelMVars := if synthLevelNorm && baseKey.type.hasLevelMVar then
        (collectLevelMVars {} baseKey.type).result
      else #[]
    let queryMVars := if synthLevelNorm && type.hasMVar then (type.collectMVars {}).result else #[]
    let (baseKey, _) := if synthLevelNorm then canonKeyLevels baseKey else (baseKey, #[])
    if synthDumpKey && nLevelMVars > 0 then
      IO.eprintln s!"ALGKEY\ttype={baseKey.type}\tLI={baseKey.localInsts.map (·.className)}\t\
        FT={baseKey.normFVarTypes}\tFV={baseKey.normFVarValues}\tSC={baseKey.activeScopedInsts.size}\t\
        LA={baseKey.localAttrInsts.size}\tEX={baseKey.isExporting}\tnorm={normCtx?.isSome}"
    let sharedKey := baseKey
    let depthKey  := { baseKey with synthPendingDepth := some synthPendingDepth }
    -- `stuckMemoFingerprint?` inspects the local instances' actual `FVarId`s, so the stuck cache
    -- must use the raw (non-normalized) key.
    let stuckKey  := { rawBaseKey with synthPendingDepth := some synthPendingDepth }
    let maxSynthPending := maxSynthPendingDepth.get (← getOptions)
    let depthShareEnabled := (← IO.getEnv "LEAN_NO_DEPTH_SHARE") != some "1"
    /-
    Applies a cache entry, or returns `none` if the entry does not answer this query, in which case
    the search has to run. A normalized key no longer determines the result, so an entry can fail to
    unify with the query; reporting that as "no instance exists" loses instances that do exist.
    -/
    let applyCached (entryHash : UInt64) (entry : SynthInstanceCacheEntry) (fromPersistent : Bool)
        (activity : SynthPendingActivity) : MetaM (Option (Option Expr)) := do
      let saved ← saveState
      -- Emitted before applying the entry, so that any nested `synthPending` traces it produces nest
      -- under it, as they did before an entry could fail to apply.
      trace[Meta.synthInstance.cache] "cached{depthSuffix}: {type}"
      -- Re-instantiate the closure-abstracted result with the current context's free variables.
      let abstResult? := match normCtx? with
        | some c => entry.result.map fun a => { a with expr := SynthNorm.reopen c.order a.expr }
        | none   => entry.result
      let some result? ← applyCachedAbstractResult? type abstResult?
        | do
          if (← IO.getEnv "LEAN_TRACE_MISAPPLY") == some "1" then
            IO.eprintln s!"MISAPPLY\n  key      = {sharedKey.type}\n  queryRAW = {type}\n  \
              queryINST= {← instantiateMVars type}\n"
          -- Undo the metavariables `openAbstractMVarsResult` minted before the failed unification.
          saved.restore
          return none
      trace[Meta.synthInstance] "result {result?} (cached)"
      recordSynthInstanceCacheStat fun s =>
        if fromPersistent then { s with hitPersistent := s.hitPersistent + 1 }
        else { s with hitTransient := s.hitTransient + 1 }
      -- Reusing the entry re-enacts its `synthPending` decisions at the current depth.
      foldActivity activity
      recordLookupOutcome sharedKey rawBaseKey entryHash (isHit := true) result? lookupT0 lookupHb0 depParent lookupMCtx
      return some result?
    let sharedEntry? ← if !depthShareEnabled then pure none else match ← findCachedResult? sharedKey with
      | some (entry, fromPersistent) =>
        match entry.relSynthPendingDepth with
        | none     => pure (some (entry, fromPersistent))
        | some rel =>
          -- Valid iff no `synthPending` invocation can reach the give-up threshold at the current
          -- depth; see `SynthInstanceCacheEntry.relSynthPendingDepth`.
          pure (if synthPendingDepth + rel ≤ maxSynthPending then some (entry, fromPersistent) else none)
      | none => pure none
    let cached? : Option (Option Expr) ←
      if let some (entry, fromPersistent) := sharedEntry? then
        applyCached (hash sharedKey) entry fromPersistent
          { maxDepth := entry.relSynthPendingDepth.map (synthPendingDepth + ·) }
      else if let some (entry, fromPersistent) ← findCachedResult? depthKey then
        -- The entry's synthesis hit the `maxSynthPendingDepth` give-up, so reusing it keeps the
        -- enclosing query depth-exact as well.
        applyCached (hash depthKey) entry fromPersistent
          { maxDepth := some synthPendingDepth, guardHit := true }
      else
        pure none
    match cached? with
    | some result? => return result?
    | none =>
      let stuckMemoEnabled := (← IO.getEnv "LEAN_NO_STUCK_MEMO") != some "1"
      if let some fingerprint := (← get).cache.synthStuck.find? stuckKey then
        -- The same query already got stuck on a metavariable; the blocking metavariable is still
        -- unassigned (otherwise the key would be more instantiated). If additionally the
        -- level-assignability fingerprint is unchanged, the search is guaranteed to get stuck
        -- again, so fail fast instead of re-running it.
        if stuckMemoEnabled && (← stuckMemoFingerprint? stuckKey) == some fingerprint then
          recordSynthInstanceCacheStat fun s => { s with hitTransient := s.hitTransient + 1 }
          trace[Meta.synthInstance.cache] "stuck (cached){depthSuffix}: {type}"
          if synthInstanceCacheStatsEnabled then
            let mut merged := depParent
            for c in ← synthDepCur.get do merged := merged.insert c
            synthDepCur.set merged
          Meta.throwIsDefEqStuck
      recordSynthInstanceCacheStat fun s => { s with miss := s.miss + 1 }
      recordSynthInstanceCacheStat fun s => match kind with
        | .noMVars             => { s with missNoMVars := s.missNoMVars + 1 }
        | .mvarsNoOutputParams => { s with missMVarsNoOut := s.missMVarsNoOut + 1 }
        | .mvarsOutputParams   => { s with missMVarsOut := s.missMVarsOut + 1 }
      if normCtx?.isNone then
        recordSynthInstanceCacheStat fun s => { s with normBailMiss := s.normBailMiss + 1 }
      let keyCls ← if synthInstanceCacheStatsEnabled then classifyMissKey sharedKey else pure 0
      let (blkBits, blkNone) ← recordMissAnalysis kind type sharedKey
      let hb0 ← IO.getNumHeartbeats
      trace[Meta.synthInstance.cache] "new{depthSuffix}: {type}"
      try
      let activityRef ← IO.mkRef {}
      let abstResult? ← withReader (fun ctx => { ctx with synthPendingActivityRef? := some activityRef }) do
        withNewMCtxDepth (allowLevelAssignments := true) do
        match kind with
        | .noMVars =>
          /-
          **Note**: The expensive `preprocessOutParam` step is morally **not** needed here because
          the output params should be uniquely determined by the input params. During type class
          resolution, definitional equality only unfolds `[reducible]` and `[instance_reducible]`
          declarations. This is a contract with our users to ensure performance is reasonable.
          However, the same `OrderDual` declaration that creates problems for `assignOutParams`
          also prevents us from using this optimization. As an example, suppose we are trying to
          synthesize
          ```
          FunLike F (OrderDual α) (OrderDual β)
          ```
          where the last two arguments of `FunLike` are output parameters. This term has no
          metavariables, and it seems natural to skip `preprocessOutParam`, which would replace
          the last two arguments with metavariables. However, if we don't replace them,
          TC resolution fails because it cannot unfold `OrderDual` since it is semireducible.

          **Note**: We should remove `preprocessOutParam` from the following line as soon as
          Mathlib refactors `OrderDual`.
          -/
          SynthInstance.main (← preprocessOutParam type) maxResultSize
        | .mvarsNoOutputParams => SynthInstance.main type maxResultSize
        | .mvarsOutputParams => SynthInstance.main (← preprocessOutParam type) maxResultSize
      let result? ← applyAbstractResult? type abstResult?
      trace[Meta.synthInstance] "result {result?}"
      let activity ← activityRef.get
      foldActivity activity
      recordMissDoneHeartbeats kind result?.isSome blkBits blkNone keyCls hb0
      -- Results whose synthesis hit the `maxSynthPendingDepth` give-up are only valid at the exact
      -- depth; all others are shared, bounded by their relative activity depth.
      let key := if activity.guardHit || !depthShareEnabled then depthKey else sharedKey
      let rel := if depthShareEnabled then activity.maxDepth.map (· - synthPendingDepth) else none
      match normCtx? with
      | none   => cacheResult key rel kind (normalized := false) abstResult? result? queryLevelMVars queryMVars
      | some c =>
        -- Store the result over the canonical closure variables; skip caching (this query only) if
        -- the result escapes the closure and so is not context-free.
        match SynthNorm.abstractValue? c abstResult? result? with
        | some (nAbstResult?, nResult?) => cacheResult key rel kind (normalized := true) nAbstResult? nResult? queryLevelMVars queryMVars
        | none => recordSynthInstanceCacheStat fun s => { s with abstractSkip := s.abstractSkip + 1 }
      recordLookupOutcome sharedKey rawBaseKey (hash key) (isHit := false) result? lookupT0 lookupHb0 depParent lookupMCtx
      return result?
      catch e =>
        if synthTraceAll then
          if let .internal id _ := e then
            if id == isDefEqStuckExceptionId then
              IO.eprintln s!"SYNTH\tSTUCK\t{← instantiateMVars rawBaseKey.type}\t=>\tSTUCK"
        if synthInstanceCacheStatsEnabled then
          let mut merged := depParent
          for c in ← synthDepCur.get do merged := merged.insert c
          synthDepCur.set merged
        recordMissStuckHeartbeats kind blkBits blkNone keyCls hb0
        if stuckMemoEnabled then
          if let .internal id _ := e then
            if id == isDefEqStuckExceptionId then
              if let some fingerprint ← stuckMemoFingerprint? stuckKey then
                modifyCache fun c => { c with synthStuck := c.synthStuck.insert stuckKey fingerprint }
        throw e

def synthInstance? (type : Expr) (maxResultSize? : Option Nat := none) : MetaM (Option Expr) := do profileitM Exception "typeclass inference" (← getOptions) (decl := type.getAppFn.constName?.getD .anonymous) do
  synthInstanceCore? type maxResultSize?

/--
  Return `LOption.some r` if succeeded, `LOption.none` if it failed, and `LOption.undef` if
  instance cannot be synthesized right now because `type` contains metavariables. -/
def trySynthInstance (type : Expr) (maxResultSize? : Option Nat := none) : MetaM (LOption Expr) := do
  catchInternalId isDefEqStuckExceptionId
    (toLOptionM <| synthInstance? type maxResultSize?)
    (fun _ => pure LOption.undef)

def throwFailedToSynthesize (type : Expr) : MetaM Expr :=
  throwError "failed to synthesize{indentExpr type}{useDiagnosticMsg}"

def synthInstance (type : Expr) (maxResultSize? : Option Nat := none) : MetaM Expr :=
  catchInternalId isDefEqStuckExceptionId
    (do
      let result? ← synthInstance? type maxResultSize?
      match result? with
      | some result => pure result
      | none        => throwFailedToSynthesize type)
    (fun _ => throwFailedToSynthesize type)

set_option compiler.ignoreBorrowAnnotation true in
@[export lean_synth_pending]
private def synthPendingImp (mvarId : MVarId) : MetaM Bool := withIncRecDepth <| mvarId.withContext do
  let mvarDecl ← mvarId.getDecl
  match mvarDecl.kind with
  | .syntheticOpaque => return false
  | _ =>
    /- Check whether the type of the given metavariable is a class or not. If yes, then try to synthesize
       it using type class resolution. We only do it for `synthetic` and `natural` metavariables. -/
    match (← isClass? mvarDecl.type) with
    | none   =>
      return false
    | some _ =>
      let depth := (← read).synthPendingDepth
      -- Record the `synthPending` decision reached at `depth`; the enclosing type class
      -- query's cache entry (if any) is only valid at depths where it comes out the same.
      if let some ref := (← read).synthPendingActivityRef? then
        ref.modify fun a => { a with maxDepth := some ((a.maxDepth.getD 0).max depth) }
      let max := maxSynthPendingDepth.get (← getOptions)
      if depth > max then
        if let some ref := (← read).synthPendingActivityRef? then
          ref.modify fun a => { a with guardHit := true }
        trace[Meta.synthPending] "too many nested synthPending invocations"
        recordSynthPendingFailure mvarDecl.type
        return false
      else
        withIncSynthPending do
          trace[Meta.synthPending] "synthPending {mkMVar mvarId}"
          let val? ← catchInternalId isDefEqStuckExceptionId (synthInstance? mvarDecl.type (maxResultSize? := none)) (fun _ => pure none)
          match val? with
          | none     =>
            return false
          | some val =>
            if (← mvarId.isAssigned) then
              return false
            else
              mvarId.assign val
              return true

register_builtin_option trace.Meta.synthInstance : Bool := {
  defValue := false
  descr := "track the backtracking attempt to synthesize type class instances"
}

builtin_initialize
  registerTraceClass `Meta.synthPending
  registerTraceClass `Meta.synthInstance.apply (inherited := true)
  registerTraceClass `Meta.synthInstance.instances (inherited := true)
  registerTraceClass `Meta.synthInstance.tryResolve (inherited := true)
  registerTraceClass `Meta.synthInstance.answer (inherited := true)
  registerTraceClass `Meta.synthInstance.resume (inherited := true)
  registerTraceClass `Meta.synthInstance.unusedArgs
  registerTraceClass `Meta.synthInstance.newAnswer
  registerTraceClass `Meta.synthInstance.cache

end Lean.Meta
