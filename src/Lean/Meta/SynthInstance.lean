/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Selsam, Leonardo de Moura

Type class instance synthesizer using tabled resolution.
-/
import Lean.Meta.Basic
import Lean.Meta.Instances
import Lean.Meta.AbstractMVars
import Lean.Meta.WHNF
import Lean.Meta.Check
import Lean.Util.Profile

namespace Lean.Meta

register_builtin_option synthInstance.maxHeartbeats : Nat := {
  defValue := 20000
  descr := "maximum amount of heartbeats per typeclass resolution problem. A heartbeat is number of (small) memory allocations (in thousands), 0 means no limit"
}

register_builtin_option synthInstance.maxSize : Nat := {
  defValue := 128
  descr := "maximum number of instances used to construct a solution in the type class instance synthesis procedure"
}

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
  | Waiter.consumerNode _ => false
  | Waiter.root           => true

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
  lmap    : HashMap LMVarId Level := {}
  emap    : HashMap MVarId Expr := {}
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
    | Level.succ v      => return u.updateSucc! (← normLevel v)
    | Level.max v w     => return u.updateMax! (← normLevel v) (← normLevel w)
    | Level.imax v w    => return u.updateIMax! (← normLevel v) (← normLevel w)
    | Level.mvar mvarId =>
      if (← getMCtx).getLevelDepth mvarId != (← getMCtx).depth then
        return u
      else
        let s ← get
        match (← get).lmap.find? mvarId with
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
    | Expr.const _ us      => return e.updateConst! (← us.mapM normLevel)
    | Expr.sort u          => return e.updateSort! (← normLevel u)
    | Expr.app f a         => return e.updateApp! (← normExpr f) (← normExpr a)
    | Expr.letE _ t v b _  => return e.updateLet! (← normExpr t) (← normExpr v) (← normExpr b)
    | Expr.forallE _ d b _ => return e.updateForallE! (← normExpr d) (← normExpr b)
    | Expr.lam _ d b _     => return e.updateLambdaE! (← normExpr d) (← normExpr b)
    | Expr.mdata _ b       => return e.updateMData! (← normExpr b)
    | Expr.proj _ _ b      => return e.updateProj! (← normExpr b)
    | Expr.mvar mvarId     =>
      if !(← mvarId.isAssignable) then
        return e
      else
        let s ← get
        match s.emap.find? mvarId with
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
  tableEntries   : HashMap Expr TableEntry       := {}

abbrev SynthM := ReaderT Context $ StateRefT State MetaM

def checkSystem : SynthM Unit := do
  Core.checkInterrupted
  Core.checkMaxHeartbeatsCore "typeclass" `synthInstance.maxHeartbeats (← read).maxHeartbeats

@[inline] def mapMetaM (f : forall {α}, MetaM α → MetaM α) {α} : SynthM α → SynthM α :=
  monadMap @f

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
      let result ← globalInstances.getUnify type tcDtConfig
      -- Using insertion sort because it is stable and the array `result` should be mostly sorted.
      -- Most instances have default priority.
      let result := result.insertionSort fun e₁ e₂ => e₁.priority < e₂.priority
      let erasedInstances ← getErasedInstances
      let mut result ← result.filterMapM fun e => match e.val with
        | Expr.const constName us =>
          if erasedInstances.contains constName then
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
            for i in [:xs.size], x in xs do
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
  return (← get).tableEntries.find? key

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
  let mvarType   ← inferType mvar
  let lctx       ← getLCtx
  let localInsts ← getLocalInstances
  forallTelescopeReducing mvarType fun xs mvarTypeBody => do
    let ⟨subgoals, instVal, instTypeBody⟩ ← getSubgoals lctx localInsts xs inst
    withTraceNode `Meta.synthInstance.tryResolve (withMCtx (← getMCtx) do
        return m!"{exceptOptionEmoji ·} {← instantiateMVars mvarTypeBody} ≟ {← instantiateMVars instTypeBody}") do
    if (← isDefEq mvarTypeBody instTypeBody) then
      let instVal ← mkLambdaFVars xs instVal
      if (← isDefEq mvar instVal) then
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
  | Waiter.root               => do
    /- Recall that we now use `ignoreLevelMVarDepth := true`. Thus, we should allow solutions
       containing universe metavariables, and not check `answer.result.paramNames.isEmpty`.
       We use `openAbstractMVarsResult` to construct the universe metavariables
       at the correct depth. -/
    if answer.result.numMVars == 0 then
      modify fun s => { s with result? := answer.result }
    else
      let (_, _, answerExpr) ← openAbstractMVarsResult answer.result
      trace[Meta.synthInstance] "skip answer containing metavariables {answerExpr}"
  | Waiter.consumerNode cNode =>
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
      (fun _ => return m!"{checkEmoji} {← instantiateMVars (← inferType cNode.mvar)}") do
    let answer ← mkAnswer cNode
    -- Remark: `answer` does not contain assignable or assigned metavariables.
    let key := cNode.key
    let entry ← getEntry key
    if isNewAnswer entry.answers answer then
      let newEntry := { entry with answers := entry.answers.push answer }
      modify fun s => { s with tableEntries := s.tableEntries.insert key newEntry }
      entry.waiters.forM (wakeUp answer)

/--
  Return `true` if a type of the form `(a_1 : A_1) → ... → (a_n : A_n) → B` has an unused argument `a_i`.

  Remark: This is syntactic check and no reduction is performed.
-/
private def hasUnusedArguments : Expr → Bool
  | Expr.forallE _ _ b _ => !b.hasLooseBVar 0 || hasUnusedArguments b
  | _ => false

/--
  If the type of the metavariable `mvar` has unused argument, return a pair `(α, transformer)`
  where `α` is a new type without the unused arguments and the `transformer` is a function for coverting a
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
          let transformer ← mkLambdaFVars #[f] (← mkLambdaFVars xs (mkAppN f ys))
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
  return (← get).generatorStack.back

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
    let inst := gNode.instances.get! idx
    let mctx := gNode.mctx
    let mvar := gNode.mvar
    discard do withMCtx mctx do
      withTraceNode `Meta.synthInstance
        (return m!"{exceptOptionEmoji ·} apply {inst.val} to {← instantiateMVars (← inferType mvar)}") do
      modifyTop fun gNode => { gNode with currInstanceIdx := idx }
      if let some (mctx, subgoals) ← tryResolve mvar inst then
        consume { key, mvar, subgoals, mctx, size := 0 }
        return some ()
      return none

def getNextToResume : SynthM (ConsumerNode × Answer) := do
  let r := (← get).resumeStack.back
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
     try
       action.run { maxResultSize := maxResultSize, maxHeartbeats := getMaxHeartbeats (← getOptions) } |>.run' {}
     catch ex =>
       if ex.isMaxHeartbeat then
         throwError "failed to synthesize{indentExpr type}\n{ex.toMessageData}"
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

private def preprocess (type : Expr) : MetaM Expr :=
  forallTelescopeReducing type fun xs type => do
    let type ← whnf type
    mkForallFVars xs type

private def preprocessLevels (us : List Level) : MetaM (List Level × Bool) := do
  let mut r := #[]
  let mut modified := false
  for u in us do
    let u ← instantiateLevelMVars u
    if u.hasMVar then
      r := r.push (← mkFreshLevelMVar)
      modified := true
    else
      r := r.push u
  return (r.toList, modified)

private partial def preprocessArgs (type : Expr) (i : Nat) (args : Array Expr) (outParamsPos : Array Nat) : MetaM (Array Expr) := do
  if h : i < args.size then
    let type ← whnf type
    match type with
    | .forallE _ d b _ => do
      let arg := args.get ⟨i, h⟩
      /-
      We should not simply check `d.isOutParam`. See `checkOutParam` and issue #1852.
      If an instance implicit argument depends on an `outParam`, it is treated as an `outParam` too.
      -/
      let arg ← if outParamsPos.contains i then mkFreshExprMVar d else pure arg
      let args := args.set ⟨i, h⟩ arg
      preprocessArgs (b.instantiate1 arg) (i+1) args outParamsPos
    | _ =>
      throwError "type class resolution failed, insufficient number of arguments" -- TODO improve error message
  else
    return args

private def preprocessOutParam (type : Expr) : MetaM Expr :=
  forallTelescope type fun xs typeBody => do
    match typeBody.getAppFn with
    | c@(Expr.const declName _) =>
      let env ← getEnv
      if let some outParamsPos := getOutParamPositions? env declName then
        unless outParamsPos.isEmpty do
          let args := typeBody.getAppArgs
          let cType ← inferType c
          let args ← preprocessArgs cType 0 args outParamsPos
          return (← mkForallFVars xs (mkAppN c args))
      return type
    | _ =>
      return type

/-!
  Remark: when `maxResultSize? == none`, the configuration option `synthInstance.maxResultSize` is used.
  Remark: we use a different option for controlling the maximum result size for coercions.
-/

def synthInstance? (type : Expr) (maxResultSize? : Option Nat := none) : MetaM (Option Expr) := do profileitM Exception "typeclass inference" (← getOptions) (decl := type.getAppFn.constName?.getD .anonymous) do
  let opts ← getOptions
  let maxResultSize := maxResultSize?.getD (synthInstance.maxSize.get opts)
  withTraceNode `Meta.synthInstance
    (return m!"{exceptOptionEmoji ·} {← instantiateMVars type}") do
  withConfig (fun config => { config with isDefEqStuckEx := true, transparency := TransparencyMode.instances,
                                          foApprox := true, ctxApprox := true, constApprox := false }) do
    let localInsts ← getLocalInstances
    let type ← instantiateMVars type
    let type ← preprocess type
    let s ← get
    let rec assignOutParams (result : Expr) : MetaM Bool := do
      let resultType ← inferType result
      /- Output parameters of local instances may be marked as `syntheticOpaque` by the application-elaborator.
         We use `withAssignableSyntheticOpaque` to make sure this kind of parameter can be assigned by the following `isDefEq`.
         TODO: rewrite this check to avoid `withAssignableSyntheticOpaque`. -/
      let defEq ← withDefault <| withAssignableSyntheticOpaque <| isDefEq type resultType
      unless defEq do
        trace[Meta.synthInstance] "{crossEmoji} result type{indentExpr resultType}\nis not definitionally equal to{indentExpr type}"
      return defEq
    match s.cache.synthInstance.find? (localInsts, type) with
    | some result =>
      trace[Meta.synthInstance] "result {result} (cached)"
      if let some inst := result then
        unless (← assignOutParams inst) do
          return none
      pure result
    | none        =>
      let result? ← withNewMCtxDepth (allowLevelAssignments := true) do
        let normType ← preprocessOutParam type
        SynthInstance.main normType maxResultSize
      let result? ← match result? with
        | none        => pure none
        | some result => do
          let (_, _, result) ← openAbstractMVarsResult result
          trace[Meta.synthInstance] "result {result}"
          if (← assignOutParams result) then
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
            pure (some result)
          else
            pure none
      modify fun s => { s with cache.synthInstance := s.cache.synthInstance.insert (localInsts, type) result? }
      pure result?

/--
  Return `LOption.some r` if succeeded, `LOption.none` if it failed, and `LOption.undef` if
  instance cannot be synthesized right now because `type` contains metavariables. -/
def trySynthInstance (type : Expr) (maxResultSize? : Option Nat := none) : MetaM (LOption Expr) := do
  catchInternalId isDefEqStuckExceptionId
    (toLOptionM <| synthInstance? type maxResultSize?)
    (fun _ => pure LOption.undef)

def synthInstance (type : Expr) (maxResultSize? : Option Nat := none) : MetaM Expr :=
  catchInternalId isDefEqStuckExceptionId
    (do
      let result? ← synthInstance? type maxResultSize?
      match result? with
      | some result => pure result
      | none        => throwError "failed to synthesize{indentExpr type}")
    (fun _ => throwError "failed to synthesize{indentExpr type}")

@[export lean_synth_pending]
private def synthPendingImp (mvarId : MVarId) : MetaM Bool := withIncRecDepth <| mvarId.withContext do
  let mvarDecl ← mvarId.getDecl
  match mvarDecl.kind with
  | MetavarKind.syntheticOpaque =>
    return false
  | _ =>
    /- Check whether the type of the given metavariable is a class or not. If yes, then try to synthesize
       it using type class resolution. We only do it for `synthetic` and `natural` metavariables. -/
    match (← isClass? mvarDecl.type) with
    | none   =>
      return false
    | some _ =>
      /- TODO: use a configuration option instead of the hard-coded limit `1`. -/
      if (← read).synthPendingDepth > 1 then
        trace[Meta.synthPending] "too many nested synthPending invocations"
        return false
      else
        withReader (fun ctx => { ctx with synthPendingDepth := ctx.synthPendingDepth + 1 }) do
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

builtin_initialize
  registerTraceClass `Meta.synthPending
  registerTraceClass `Meta.synthInstance
  registerTraceClass `Meta.synthInstance.instances (inherited := true)
  registerTraceClass `Meta.synthInstance.tryResolve (inherited := true)
  registerTraceClass `Meta.synthInstance.resume (inherited := true)
  registerTraceClass `Meta.synthInstance.unusedArgs
  registerTraceClass `Meta.synthInstance.newAnswer

end Lean.Meta
