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
import Init.While
import Lean.Util.CollectFVars

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

register_builtin_option debug.synthInstance.checkCacheHits : Bool := {
  defValue := false
  descr := "differentially validate type class resolution cache hits: re-run every served query from scratch and panic if the recomputed result differs from the cached one, which means a dependency of the entry was not recorded (development soak check; roughly doubles resolution cost)"
}

namespace SynthInstance

def getMaxHeartbeats (opts : Options) : Nat :=
  -- Unrestricted read: the limit is part of the resolution cache key
  -- (`SynthInstanceCacheKey.limits`).
  synthInstance.maxHeartbeats.getUnrestricted opts * 1000

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
    if (← getRecordedOption backward.synthInstance.canonInstances) then
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
Returns `true` if the `check` at `applyAbstractResult?` may have observable side effects
for `result`. The unifications performed by the check operate on expressions derived from
`result` itself, from the types (and values) of its free variables, and from constant type
schemes instantiated with `result`'s own universe levels. Thus, if no metavariable is
reachable through `result` or through the (transitive) types and values of its free
variables, every unification is between ground expressions and cannot assign anything, so
the check is redundant. Note that mere absence of metavariables in `result` is not enough:
in issue #796, the universe constraint flows through the type `E.{?v} a` of a local
instance occurring in `result`.
-/
private def checkMayHaveSideEffects (result : Expr) : MetaM Bool := do
  if result.hasExprMVar || result.hasLevelMVar then return true
  let mut s := collectFVars {} result
  let mut i := 0
  while h : i < s.fvarIds.size do
    let localDecl ← s.fvarIds[i].getDecl
    let type ← instantiateMVars localDecl.type
    if type.hasExprMVar || type.hasLevelMVar then return true
    s := collectFVars s type
    if let some value := localDecl.value? then
      let value ← instantiateMVars value
      if value.hasExprMVar || value.hasLevelMVar then return true
      s := collectFVars s value
    i := i + 1
  return false

/--
Auxiliary function for converting the `AbstractMVarsResult` returned by `SynthInstance.main` into an `Expr`.
-/
private def applyAbstractResult? (type : Expr) (abstResult? : Option AbstractMVarsResult) : MetaM (Option Expr) := do
  let some abstResult := abstResult? | return none
  let (_, _, result) ← openAbstractMVarsResult abstResult
  unless (← assignOutParams type result) do return none
  let result ← instantiateMVars result
  unless (← checkMayHaveSideEffects result) do
    return some result
  /- We use `check` to propagate universe constraints implied by the `result`.
      Recall that we use `allowLevelAssignments := true` which allows universe metavariables in the current depth to be assigned,
      but these assignments are discarded by `withNewMCtxDepth`.

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

      **Note**: We tried to skip this `check` by tracking whether a universe metavariable
      from a lower depth was assigned during the search (a flag set by the level-unification
      procedures; such assignments can only happen during TC resolution and are exactly the
      ones discarded by `withNewMCtxDepth`). The tracking is insufficient: without
      `checkMayHaveSideEffects`, a clean Mathlib build produced 5 failures
      (`CategoryTheory/Limits/FilteredColimitCommutesProduct`, `CategoryTheory/Limits/Presheaf`,
      `Topology/Category/CompHausLike/SigmaComparison`, `Algebra/Category/ModuleCat/Colimits`,
      `Analysis/CStarAlgebra/ContinuousFunctionalCalculus/Isometric`), ranging from
      declarations with leaked universe metavariables and kernel type mismatches to
      "don't know how to synthesize implicit argument". We suspect the situation is
      analogous to the `isDefEq` test at `tryResolve` (see the **Note** there): the `check`
      produces unintended side effects (e.g., `trySynthPending` on expression metavariables,
      universe assignments the search itself never derived) that these few Mathlib places
      rely on, possibly by accident. We should diagnose whether they work by accident and,
      if so, fix Mathlib and remove (or further weaken) this `check`.
  -/
  check result
  return some result

/-- Returns whether every recorded lookup in `log` gives the same answer in `opts`. -/
private def validOptionAccesses (opts : Options) (log : SynthOptionAccessLog) : Bool :=
  log.all fun a => opts.findUnrestricted? a.name == a.value

/--
Merges the environment dependencies observed by a nested query (or served from a used cache
entry) into the enclosing query's accumulator. The enclosing query keeps its own
`changeLogPos` and `tcGen`: they were captured when that query started, and the merged
dependencies are validated against them like the query's own observations.
-/
private def _root_.Lean.SynthEnvDeps.mergeInto (child parent : SynthEnvDeps) : SynthEnvDeps :=
  let options := child.options.foldl (init := parent.options) fun l a =>
    if l.any (·.name == a.name) then l else l.push a
  let extGens := child.extGens.foldl (init := parent.extGens) fun l d =>
    if l.any (·.1 == d.1) then l else l.push d
  { parent with options, extGens }

/--
Identity of two dependency logs for entry replacement in `insertCachedResult`: same option
answers and same dependency *shape* (same extensions and reducibility declarations observed).
The observed generations and statuses are deliberately not part of the identity: a fresh
observation with the same shape supersedes the old entry, whose generations can never recur.
-/
private def sameDepIdentity (a b : SynthEnvDeps) : Bool :=
  a.options == b.options
  && a.extGens.size == b.extGens.size
  && a.extGens.all (fun d => b.extGens.any (·.1 == d.1))

/--
Inserts a result into the type class resolution cache: always into the transient
`Meta.Cache.synthInstance` tier, which has the lifetime of the current `Meta.State`, and
additionally into the persistent tier if `persist` is true.

Only context-free entries may be persisted: the key must not contain metavariables and the result
must be closed. Results with abstracted metavariables are only valid relative to the elaboration
context that created them: their degrees of freedom (e.g. universe metavariables not determined
by the key, cf. `Small`) are resolved by ambient constraints, so reusing them in a different
context can produce incorrectly instantiated terms.

A persistent insertion is rolled back together with the environment (see
`Environment.synthCache`); the transient copy then still serves the entry for the rest of the
command, as `Meta.SavedState.restore` deliberately does not restore `Meta.Cache`. Without it,
backtracking-heavy elaboration (e.g. tactics trying alternatives) would re-run every failed
attempt's typeclass queries from scratch.
-/
private def insertCachedResult (key : SynthInstanceCacheKey) (log : SynthEnvDeps)
    (result? : Option AbstractMVarsResult) (persist : Bool) : MetaM Unit := do
  -- One entry per observed dependency combination; replace an entry with the same identity.
  let upsert (c : SynthInstanceCache) : SynthInstanceCache :=
    c.insert key <| (log, result?) :: (c.find? key |>.getD [] |>.filter fun e => !sameDepIdentity e.1 log)
  if persist then
    -- Modify the environment directly instead of via `Meta.modifyEnv`, which would reset the
    -- `Meta.Cache` caches.
    modifyThe Core.State fun s =>
      { s with env := s.env.setSynthCache (upsert s.env.synthCache) }
  modifyCache fun c => { c with synthInstance := upsert c.synthInstance }

/--
Validates a cache entry's recorded dependencies against the current context. Returns `none` if
any recorded answer has changed; otherwise the entry may be used, and the returned Boolean
indicates the log was *re-stamped*: `Environment.synthDepGen` had moved, all recorded
dependencies re-answered identically, and the log now carries the current stamps (including
the reducibility log position and birth watermark, so each log segment is scanned at most once
per entry). The caller re-inserts a re-stamped entry.

The status re-asks may record into the armed query's accumulator, which is benign: it
over-approximates the current query's dependencies.
-/
private def validateDeps? (opts : Options) (env : Environment)
    (log : SynthEnvDeps) : BaseIO (Option (SynthEnvDeps × Bool)) := do
  unless validOptionAccesses opts log.options do return none
  -- Global short-circuit: while `Environment.synthDepGen` is unchanged, no recorded environment
  -- dependency can have changed and the per-dependency checks are skipped.
  if log.tcGen == env.synthDepGen then
    return some (log, false)
  for (idx, gen) in log.extGens do
    unless (← EnvExtension.getRecordedGen env idx) == gen do return none
  unless env.checkSynthChangeLog log.changeLogPos log.constBirthW do return none
  return some ({ log with
    tcGen := env.synthDepGen
    changeLogPos := env.synthChangeLog.size
    constBirthW := env.constBirthGen }, true)

/--
Returns the type class resolution cache entry for `key` from the transient
(`Meta.Cache.synthInstance`) or persistent (`Environment.synthCache`) tier, together with its
recorded dependencies. Only entries whose recorded dependencies give the same answers in the
current context are considered (`validateDeps?`); a re-stamped entry is re-inserted into its
tier. See `SynthInstanceCache`.
-/
private def findCachedResult? (key : SynthInstanceCacheKey) :
    MetaM (Option (SynthEnvDeps × Option AbstractMVarsResult)) := do
  let opts ← getOptions
  let env ← getEnv
  let findIn (c : SynthInstanceCache) :
      BaseIO (Option (SynthEnvDeps × Option AbstractMVarsResult × Bool)) := do
    let some entries := c.find? key | return none
    for (log, val?) in entries do
      if let some (log, restamped) ← validateDeps? opts env log then
        return some (log, val?, restamped)
    return none
  if let some (log, val?, restamped) ← findIn (← get).cache.synthInstance then
    if restamped then
      insertCachedResult key log val? (persist := false)
    return some (log, val?)
  if let some (log, val?, restamped) ← findIn env.synthCache then
    if restamped then
      insertCachedResult key log val? (persist := true)
    return some (log, val?)
  return none

/--
Auxiliary function for converting a cached `AbstractMVarsResult` returned by `SynthInstance.main` into an `Expr`.
This function tries to avoid the potentially expensive `check` at `applyCachedAbstractResult?`.
-/
private def applyCachedAbstractResult? (type : Expr) (abstResult? : Option AbstractMVarsResult) : MetaM (Option Expr) := do
  let some abstResult := abstResult? | return none
  if abstResult.numMVars == 0 && abstResult.paramNames.isEmpty then
    /-
    Result does not introduce new metavariables, thus we don't need to perform (again)
    the `check` at `applyAbstractResult?`.
    This is an optimization.
    -/
    unless (← assignOutParams type abstResult.expr) do
      return none
    return some abstResult.expr
  else
    applyAbstractResult? type abstResult?

/-- Helper function for caching synthesized type class instances. -/
private def cacheResult (cacheKey : SynthInstanceCacheKey) (log : SynthEnvDeps) (kind : PreprocessKind) (normalized : Bool) (abstResult? : Option AbstractMVarsResult) (result? : Option Expr) : MetaM Unit := do
  -- The stored value: for a closed result we store the concrete `result` expr with an empty
  -- `AbstractMVarsResult` so that `applyCachedAbstractResult?` can skip re-`check`ing it.
  let value? :=
    match abstResult? with
    | none => none
    | some abstResult =>
      if abstResult.numMVars == 0 && abstResult.paramNames.isEmpty && kind matches .noMVars | .mvarsNoOutputParams then
        result?.map fun result => { expr := result, paramNames := #[], mvars := #[] }
      else
        some abstResult
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
    (value?.all fun r => r.numMVars == 0 && r.paramNames.isEmpty && !r.expr.hasFVar)
  insertCachedResult cacheKey log value? (persist := persist)

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
  unless e.hasFVar do return e
  match e with
  | .fvar id =>
    if let some i := (← get).fmap.find? id then
      return .fvar (canonFVarId i)
    -- `preprocess` puts this marker in output-parameter positions; it is a constant, not a
    -- variable of the local context, and must not be renamed (nor bail the normalization).
    if id.name == `__wild__ then return e
    match (← read).find? id with
    | none =>
      modify fun s => { s with bail := true }
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
      if type.hasMVar || (match value? with | some v => v.hasMVar | none => false) then
        modify fun s => { s with bail := true }
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
      return memo.closure?
  let go : M LocalInstances :=
    localInsts.mapM fun li => return { li with fvar := ← normExpr li.fvar }
  let (canonLocalInsts, st) ← go.run lctx |>.run {}
  let closure? :=
    if st.bail then none
    else some { fmap := st.fmap, order := st.order, types := st.types, values := st.values,
                canonLocalInsts }
  modifyCache fun c =>
    { c with synthNormClosure := some { localInsts, mvarTyped := st.mvarTyped, closure? } }
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
  let some closure ← getClosure? localInsts | return none
  let lctx ← getLCtx
  -- Seed from the memoized closure; the query type may extend it with further free variables.
  let st0 : State := { fmap := closure.fmap, order := closure.order, types := closure.types,
                       values := closure.values }
  let (normType, st) ← (normExpr cacheKeyType).run lctx |>.run st0
  if st.bail then return none
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
The `Meta.Config` used for all type class resolution. The ambient configuration is replaced
wholesale rather than adjusted: resolution results are cached across contexts and commands with no
configuration component in the cache key, so any ambient configuration that influenced the search
(e.g. `canUnfoldPredicateConfig` set by `simp`) would leak between contexts through the cache.
Search-relevant state that must flow in from the caller is context, not configuration, and is part
of the cache key (e.g. `synthPendingDepth`, the relevant options).
-/
private def synthInstanceConfig : Config :=
  { isDefEqStuckEx := true, transparency := .instances,
    foApprox := true, ctxApprox := true, constApprox := false, univApprox := false }

/--
Marks the query as recording on the environment (`Environment.synthRecording`) without
resetting `Meta.Cache` (which `Meta.modifyEnv` would).
-/
private def setSynthRecording (recording : Bool) : MetaM Unit :=
  modifyThe Core.State fun s => { s with env := s.env.setSynthRecording recording }

def synthInstanceCore? (type : Expr) (maxResultSize? : Option Nat := none) : MetaM (Option Expr) := do
  -- For a nested query this read happens under the enclosing query's restriction and is recorded
  -- as its dependency: the value determines the nested query's cache key.
  let maxResultSize ← match maxResultSize? with
    | some n => pure n
    | none   => getRecordedOption synthInstance.maxSize
  -- The query's dependencies: result-relevant option lookups on the search path go through the
  -- recording accessors (`getRecordedOption`), and observed environment dependencies are
  -- recorded directly; both flow into the accumulator `Meta.Cache.synthEnvDeps`, which becomes
  -- the cache entry's dependency log, see `SynthInstanceCache`. The enclosing query's
  -- accumulator (if any) is saved here and the nested query's effective dependencies are
  -- merged into it on exit (`finally` below): the enclosing query observed the result.
  let parentDeps := (← get).cache.synthEnvDeps
  let parentRecording := (← getEnv).synthRecording
  let fresh : SynthEnvDeps :=
    { tcGen := (← getEnv).synthDepGen
      changeLogPos := (← getEnv).synthChangeLog.size
      constBirthW := (← getEnv).constBirthGen }
  modifyCache fun c => { c with synthEnvDeps := fresh }
  setSynthRecording true
  try
  -- Restrict the ambient options: result-relevant by-name reads on the search path are diverted
  -- to the recording accessors by construction (a plain read panics), so the recorded log
  -- captures every option that can affect the result. See `OptionsRestriction.tcResolution`.
  withOptions (·.restrict .tcResolution) do
  -- Resolve the per-step definitional-equality flags once; they are part of the cache key
  -- rather than recorded dependencies, so the raw reads are not logged. See `SynthDefEqFlags`.
  let opts ← getOptions
  let getB (n : Name) (d : Bool) : Bool :=
    ((opts.findUnrestricted? n).bind KVMap.Value.ofDataValue?).getD d
  let flags : SynthDefEqFlags := {
    respectTransparency      := getB `backward.isDefEq.respectTransparency true
    respectTransparencyTypes := getB `backward.isDefEq.respectTransparency.types true
    implicitBump             := getB `backward.isDefEq.implicitBump true
    reducibleClassField      := getB `backward.whnf.reducibleClassField true
    lazyProjDelta            := getB `backward.isDefEq.lazyProjDelta true
    lazyWhnfCore             := getB `backward.isDefEq.lazyWhnfCore true
    smartUnfolding           := getB `smartUnfolding true
  }
  -- Resource limits are part of the cache key (`SynthInstanceCacheKey.limits`): exceeding one
  -- throws and results are only stored on the success path, so a limit cannot influence a
  -- stored result, and keying by them makes that structural. Read by name because their
  -- accessors live in modules this one does not import.
  let getN (n : Name) (d : Nat) : Nat :=
    ((opts.findUnrestricted? n).bind KVMap.Value.ofDataValue?).getD d
  let limits : SynthLimits := {
    maxHeartbeats           := getN `maxHeartbeats 200000
    synthInstanceHeartbeats := getN `synthInstance.maxHeartbeats 20000
    maxRecDepth             := getN `maxRecDepth 512
    exponentiationThreshold := getN `exponentiation.threshold 256
  }
  withReader (fun ctx => { ctx with synthDefEqFlags? := some flags }) do
  withTraceNode `Meta.synthInstance
    (fun _ => return m!"{← instantiateMVars type}") do
  withConfig (fun _ => synthInstanceConfig) do
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
    -- The instance-table generation is recorded once per query here, covering every read of
    -- the table on the search path.
    recordExtGenAccess instanceExtension.ext.toEnvExtension.idx
    let insts := instanceExtension.getState (recorded := true) (← getEnv)
    let cacheKey := { localInsts, type := cacheKeyType, synthPendingDepth := (← read).synthPendingDepth,
                      activeScopedInsts := instanceExtension.getActiveScopesWithEntries (recorded := true) (← getEnv),
                      localAttrInsts := insts.localInstanceNames,
                      erasedInsts := if insts.erased.isEmpty then #[]
                        else insts.erased.fold (init := #[]) (·.push ·) |>.qsort Name.quickLt,
                      maxResultSize, defEqFlags := flags, limits,
                      isExporting := (← getEnv).isExporting }
    let cacheKey := match normCtx? with
      | some c => { cacheKey with localInsts := c.canonLocalInsts, type := c.normType, normFVarTypes := c.fvarTypes, normFVarValues := c.fvarValues }
      | none   => cacheKey
    let runSearch : MetaM (Option AbstractMVarsResult) :=
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
    -- Differential validation of a served hit (`debug.synthInstance.checkCacheHits`): recompute
    -- the query from scratch and compare against the served result. The recompute bypasses the
    -- entry under test by construction (the search body performs no cache lookup), and its
    -- recorded dependencies flow into the current accumulator, which only strengthens the
    -- entry's log. Raw `toString` is used for reporting: the pretty printer reads options by
    -- name, which the ambient restriction diverts.
    let checkHit (served? : Option AbstractMVarsResult) : MetaM Unit := do
      -- deliberately unrestricted read: purely diagnostic, cannot influence a cached result
      unless debug.synthInstance.checkCacheHits.getUnrestricted (← getOptions) do return
      -- Fresh heartbeat budget: the recompute must not consume the query's own allowance. The
      -- check is observation-only, so recompute exceptions are reported instead of propagated:
      -- a search that throws where the cache had an answer is itself a divergence.
      let fresh?? : Except String (Option AbstractMVarsResult) ←
        try
          .ok <$> withCurrHeartbeats runSearch
        catch ex => do
          let msg ← ex.toMessageData.toString
          pure <| .error s!"exception: {msg}"
      let pp : Option AbstractMVarsResult → String
        | none => "none"
        | some r => toString r.expr
      let mismatch? : Option String := match fresh?? with
        | .error e => some e
        | .ok fresh? =>
          let same := match served?, fresh? with
            | none, none => true
            | some a, some b => a.numMVars == b.numMVars && a.paramNames == b.paramNames && a.expr == b.expr
            | _, _ => false
          if same then none else some (pp fresh?)
      if let some fresh := mismatch? then
        -- the panic is the branch result: an unused pure binding would be dead-code-eliminated
        panic! s!"type class resolution cache hit differs from recomputation for\n  \
          {toString type}\ncached: {pp served?}\nrecomputed: {fresh}\n\
          an environment dependency of the served entry was not recorded; see \
          `Lean.EnvExtension.trackGen`"
    match ← findCachedResult? cacheKey with
    | some (entryLog, abstResult?) =>
      trace[Meta.synthInstance.cache] "cached: {type}"
      -- The used entry's dependencies become dependencies of this query.
      modifyCache fun c => { c with synthEnvDeps := entryLog.mergeInto c.synthEnvDeps }
      -- Re-instantiate the closure-abstracted result with the current context's free variables.
      let abstResult? := match normCtx? with
        | some c => abstResult?.map fun a => { a with expr := SynthNorm.reopen c.order a.expr }
        | none   => abstResult?
      checkHit abstResult?
      let result? ← applyCachedAbstractResult? type abstResult?
      trace[Meta.synthInstance] "result {result?} (cached)"
      return result?
    | none =>
      trace[Meta.synthInstance.cache] "new: {type}"
      let abstResult? ← runSearch
      let result? ← applyAbstractResult? type abstResult?
      trace[Meta.synthInstance] "result {result?}"
      let log : SynthEnvDeps := (← get).cache.synthEnvDeps
      match normCtx? with
      | none   => cacheResult cacheKey log kind (normalized := false) abstResult? result?
      | some c =>
        -- Store the result over the canonical closure variables; skip caching (this query only) if
        -- the result escapes the closure and so is not context-free.
        match SynthNorm.abstractValue? c abstResult? result? with
        | some (nAbstResult?, nResult?) => cacheResult cacheKey log kind (normalized := true) nAbstResult? nResult?
        | none => pure ()
      return result?
  finally
    -- Restore the enclosing accumulator, merging this query's effective dependencies into it.
    let childDeps := (← get).cache.synthEnvDeps
    setSynthRecording parentRecording
    modifyCache fun c => { c with synthEnvDeps :=
      if parentRecording then childDeps.mergeInto parentDeps else parentDeps }

def synthInstance? (type : Expr) (maxResultSize? : Option Nat := none) : MetaM (Option Expr) := do
  -- Profiling is a display boundary: strip the access restriction of an enclosing query, whose
  -- options would otherwise reach the profiler's by-name reads (via `lean_profileit`).
  profileitM Exception "typeclass inference" ((← getOptions).restrict .none) (decl := type.getAppFn.constName?.getD .anonymous) do
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
      let max ← getRecordedOption maxSynthPendingDepth
      if (← read).synthPendingDepth > max then
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
