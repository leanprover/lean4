/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Selsam, Leonardo de Moura

Type class instance synthesizer using tabled resolution.
-/
import Lean.Meta.Basic
import Lean.Meta.Instances
import Lean.Meta.LevelDefEq
import Lean.Meta.AbstractMVars
import Lean.Meta.WHNF
import Lean.Util.Profile

namespace Lean.Meta

register_builtin_option synthInstance.maxHeartbeats : Nat := {
  defValue := 500
  descr := "maximum amount of heartbeats per typeclass resolution problem. A heartbeat is number of (small) memory allocations (in thousands), 0 means no limit"
}

register_builtin_option synthInstance.maxSize : Nat := {
  defValue := 128
  descr := "maximum number of instances used to construct a solution in the type class instance synthesis procedure"
}
namespace SynthInstance

def getMaxHeartbeats (opts : Options) : Nat :=
  synthInstance.maxHeartbeats.get opts * 1000

open Std (HashMap)

builtin_initialize inferTCGoalsRLAttr : TagAttribute ←
  registerTagAttribute `inferTCGoalsRL "instruct type class resolution procedure to solve goals from right to left for this instance"

def hasInferTCGoalsRLAttribute (env : Environment) (constName : Name) : Bool :=
  inferTCGoalsRLAttr.hasTag env constName

structure GeneratorNode where
  mvar            : Expr
  key             : Expr
  mctx            : MetavarContext
  instances       : Array Expr
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

/-
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
  lmap    : HashMap MVarId Level := {}
  emap    : HashMap MVarId Expr := {}

abbrev M := ReaderT MetavarContext (StateM State)

partial def normLevel (u : Level) : M Level := do
  if !u.hasMVar then
    pure u
  else match u with
    | Level.succ v _      => return u.updateSucc! (← normLevel v)
    | Level.max v w _     => return u.updateMax! (← normLevel v) (← normLevel w)
    | Level.imax v w _    => return u.updateIMax! (← normLevel v) (← normLevel w)
    | Level.mvar mvarId _ =>
      let mctx ← read
      if !mctx.isLevelAssignable mvarId then
        pure u
      else
        let s ← get
        match s.lmap.find? mvarId with
        | some u' => pure u'
        | none    =>
          let u' := mkLevelParam $ Name.mkNum `_tc s.nextIdx
          modify fun s => { s with nextIdx := s.nextIdx + 1, lmap := s.lmap.insert mvarId u' }
          pure u'
    | u => pure u

partial def normExpr (e : Expr) : M Expr := do
  if !e.hasMVar then
    pure e
  else match e with
    | Expr.const _ us _    => return e.updateConst! (← us.mapM normLevel)
    | Expr.sort u _        => return e.updateSort! (← normLevel u)
    | Expr.app f a _       => return e.updateApp! (← normExpr f) (← normExpr a)
    | Expr.letE _ t v b _  => return e.updateLet! (← normExpr t) (← normExpr v) (← normExpr b)
    | Expr.forallE _ d b _ => return e.updateForallE! (← normExpr d) (← normExpr b)
    | Expr.lam _ d b _     => return e.updateLambdaE! (← normExpr d) (← normExpr b)
    | Expr.mdata _ b _     => return e.updateMData! (← normExpr b)
    | Expr.proj _ _ b _    => return e.updateProj! (← normExpr b)
    | Expr.mvar mvarId _   =>
      let mctx ← read
      if !mctx.isExprAssignable mvarId then
        pure e
      else
        let s ← get
        match s.emap.find? mvarId with
        | some e' => pure e'
        | none    => do
          let e' := mkFVar { name := Name.mkNum `_tc s.nextIdx }
          modify fun s => { s with nextIdx := s.nextIdx + 1, emap := s.emap.insert mvarId e' }
          pure e'
    | _ => pure e

end MkTableKey

/- Remark: `mkTableKey` assumes `e` does not contain assigned metavariables. -/
def mkTableKey (mctx : MetavarContext) (e : Expr) : Expr :=
  MkTableKey.normExpr e mctx |>.run' {}

structure Answer where
  result     : AbstractMVarsResult
  resultType : Expr
  size       : Nat

instance : Inhabited Answer where
  default := { result := arbitrary, resultType := arbitrary, size := 0 }

structure TableEntry where
  waiters : Array Waiter
  answers : Array Answer := #[]

structure Context where
  maxResultSize : Nat
  maxHeartbeats : Nat

/-
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

def checkMaxHeartbeats : SynthM Unit := do
  Core.checkMaxHeartbeatsCore "typeclass" `synthInstance.maxHeartbeats (← read).maxHeartbeats

@[inline] def mapMetaM (f : forall {α}, MetaM α → MetaM α) {α} : SynthM α → SynthM α :=
  monadMap @f

instance : Inhabited (SynthM α) where
  default := fun _ _ => arbitrary

/-- Return globals and locals instances that may unify with `type` -/
def getInstances (type : Expr) : MetaM (Array Expr) := do
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
      let result ← result.filterMapM fun e => match e.val with
        | Expr.const constName us _ =>
          if erasedInstances.contains constName then
            return none
          else
            return some <| e.val.updateConst! (← us.mapM (fun _ => mkFreshLevelMVar))
        | _ => panic! "global instance is not a constant"
      trace[Meta.synthInstance.globalInstances] "{type}, {result}"
      let result := localInstances.foldl (init := result) fun (result : Array Expr) linst =>
        if linst.className == className then result.push linst.fvar else result
      pure result

def mkGeneratorNode? (key mvar : Expr) : MetaM (Option GeneratorNode) := do
  let mvarType  ← inferType mvar
  let mvarType  ← instantiateMVars mvarType
  let instances ← getInstances mvarType
  if instances.isEmpty then
    pure none
  else
    let mctx ← getMCtx
    pure $ some {
      mvar            := mvar,
      key             := key,
      mctx            := mctx,
      instances       := instances,
      currInstanceIdx := instances.size
    }

/-- Create a new generator node for `mvar` and add `waiter` as its waiter.
    `key` must be `mkTableKey mctx mvarType`. -/
def newSubgoal (mctx : MetavarContext) (key : Expr) (mvar : Expr) (waiter : Waiter) : SynthM Unit :=
  withMCtx mctx do
    trace[Meta.synthInstance.newSubgoal] key
    match (← mkGeneratorNode? key mvar) with
    | none      => pure ()
    | some node =>
      let entry : TableEntry := { waiters := #[waiter] }
      modify fun s =>
       { s with
         generatorStack := s.generatorStack.push node,
         tableEntries   := s.tableEntries.insert key entry }

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
    return mkTableKey mctx mvarType

/- See `getSubgoals` and `getSubgoalsAux`

   We use the parameter `j` to reduce the number of `instantiate*` invocations.
   It is the same approach we use at `forallTelescope` and `lambdaTelescope`.
   Given `getSubgoalsAux args j subgoals instVal type`,
   we have that `type.instantiateRevRange j args.size args` does not have loose bound variables. -/
structure SubgoalsResult where
  subgoals     : List Expr
  instVal      : Expr
  instTypeBody : Expr

private partial def getSubgoalsAux (lctx : LocalContext) (localInsts : LocalInstances) (xs : Array Expr)
    : Array Expr → Nat → List Expr → Expr → Expr → MetaM SubgoalsResult
  | args, j, subgoals, instVal, Expr.forallE n d b c => do
    let d        := d.instantiateRevRange j args.size args
    let mvarType ← mkForallFVars xs d
    let mvar     ← mkFreshExprMVarAt lctx localInsts mvarType
    let arg      := mkAppN mvar xs
    let instVal  := mkApp instVal arg
    let subgoals := if c.binderInfo.isInstImplicit then mvar::subgoals else subgoals
    let args     := args.push (mkAppN mvar xs)
    getSubgoalsAux lctx localInsts xs args j subgoals instVal b
  | args, j, subgoals, instVal, type => do
    let type := type.instantiateRevRange j args.size args
    let type ← whnf type
    if type.isForall then
      getSubgoalsAux lctx localInsts xs args args.size subgoals instVal type
    else
      pure ⟨subgoals, instVal, type⟩

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
def getSubgoals (lctx : LocalContext) (localInsts : LocalInstances) (xs : Array Expr) (inst : Expr) : MetaM SubgoalsResult := do
  let instType ← inferType inst
  let result ← getSubgoalsAux lctx localInsts xs #[] 0 [] inst instType
  match inst.getAppFn with
  | Expr.const constName _ _ =>
    let env ← getEnv
    if hasInferTCGoalsRLAttribute env constName then
      pure result
    else
      pure { result with subgoals := result.subgoals.reverse }
  | _ => pure result

def tryResolveCore (mvar : Expr) (inst : Expr) : MetaM (Option (MetavarContext × List Expr)) := do
  let mvar ← instantiateMVars mvar
  if !(← hasAssignableMVar mvar) then
    /- The metavariable `mvar` may have been assinged when solving typing constraints.
       This may happen when a local instance type depends on other local instances.
       For example, in Mathlib, we have
       ```
       @Submodule.setLike : {R : Type u_1} → {M : Type u_2} →
         [_inst_1 : Semiring R] →
         [_inst_2 : AddCommMonoid M] →
         [_inst_3 : @ModuleS R M _inst_1 _inst_2] →
         SetLike (@Submodule R M _inst_1 _inst_2 _inst_3) M
       ```
       TODO: discuss what is the correct behavior here. There are other possibilities.
       1) We could try to synthesize the instances `_inst_1` and `_inst_2` and check
          whether it is defeq to the one inferred by typing constraints. That is, we
          remove this `if`-statement. We discarded this one because some Mathlib theorems
          failed to be elaborated using it.
       2) Generate an error/warning message when instances such as `Submodule.setLike` are declared,
          and instruct user to use `{}` binder annotation for `_inst_1` `_inst_2`.
     -/
    return some ((← getMCtx), [])
  let mvarType   ← inferType mvar
  let lctx       ← getLCtx
  let localInsts ← getLocalInstances
  forallTelescopeReducing mvarType fun xs mvarTypeBody => do
    let ⟨subgoals, instVal, instTypeBody⟩ ← getSubgoals lctx localInsts xs inst
    trace[Meta.synthInstance.tryResolve] "{mvarTypeBody} =?= {instTypeBody}"
    if (← isDefEq mvarTypeBody instTypeBody) then
      let instVal ← mkLambdaFVars xs instVal
      if (← isDefEq mvar instVal) then
        trace[Meta.synthInstance.tryResolve] "success"
        pure (some ((← getMCtx), subgoals))
      else
        trace[Meta.synthInstance.tryResolve] "failure assigning"
        pure none
    else
      trace[Meta.synthInstance.tryResolve] "failure"
      pure none

/--
  Try to synthesize metavariable `mvar` using the instance `inst`.
  Remark: `mctx` contains `mvar`.
  If it succeeds, the result is a new updated metavariable context and a new list of subgoals.
  A subgoal is created for each instance implicit parameter of `inst`. -/
def tryResolve (mctx : MetavarContext) (mvar : Expr) (inst : Expr) : SynthM (Option (MetavarContext × List Expr)) :=
  traceCtx `Meta.synthInstance.tryResolve <| withMCtx mctx <| tryResolveCore mvar inst

/--
  Assign a precomputed answer to `mvar`.
  If it succeeds, the result is a new updated metavariable context and a new list of subgoals. -/
def tryAnswer (mctx : MetavarContext) (mvar : Expr) (answer : Answer) : SynthM (Option MetavarContext) :=
  withMCtx mctx do
    let (_, _, val) ← openAbstractMVarsResult answer.result
    if (← isDefEq mvar val) then
      pure (some (← getMCtx))
    else
      pure none

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
      pure ()
  | Waiter.consumerNode cNode =>
    modify fun s => { s with resumeStack := s.resumeStack.push (cNode, answer) }

def isNewAnswer (oldAnswers : Array Answer) (answer : Answer) : Bool :=
  oldAnswers.all fun oldAnswer => do
    -- Remark: isDefEq here is too expensive. TODO: if `==` is too imprecise, add some light normalization to `resultType` at `addAnswer`
    -- iseq ← isDefEq oldAnswer.resultType answer.resultType; pure (!iseq)
    oldAnswer.resultType != answer.resultType

private def mkAnswer (cNode : ConsumerNode) : MetaM Answer :=
  withMCtx cNode.mctx do
    traceM `Meta.synthInstance.newAnswer do m!"size: {cNode.size}, {← inferType cNode.mvar}"
    let val ← instantiateMVars cNode.mvar
    trace[Meta.synthInstance.newAnswer] "val: {val}"
    let result ← abstractMVars val -- assignable metavariables become parameters
    let resultType ← inferType result.expr
    pure { result := result, resultType := resultType, size := cNode.size + 1 }

/--
  Create a new answer after `cNode` resolved all subgoals.
  That is, `cNode.subgoals == []`.
  And then, store it in the tabled entries map, and wakeup waiters. -/
def addAnswer (cNode : ConsumerNode) : SynthM Unit := do
  if cNode.size ≥ (← read).maxResultSize then
    traceM `Meta.synthInstance.discarded do m!"size: {cNode.size} ≥ {(← read).maxResultSize}, {← inferType cNode.mvar}"
    return ()
  else
    let answer ← mkAnswer cNode
    -- Remark: `answer` does not contain assignable or assigned metavariables.
    let key := cNode.key
    let entry ← getEntry key
    if isNewAnswer entry.answers answer then
      let newEntry := { entry with answers := entry.answers.push answer }
      modify fun s => { s with tableEntries := s.tableEntries.insert key newEntry }
      entry.waiters.forM (wakeUp answer)

/-- Process the next subgoal in the given consumer node. -/
def consume (cNode : ConsumerNode) : SynthM Unit :=
  match cNode.subgoals with
  | []      => addAnswer cNode
  | mvar::_ => do
     let waiter := Waiter.consumerNode cNode
     let key ← mkTableKeyFor cNode.mctx mvar
     let entry? ← findEntry? key
     match entry? with
     | none       => newSubgoal cNode.mctx key mvar waiter
     | some entry => modify fun s =>
       { s with
         resumeStack  := entry.answers.foldl (fun s answer => s.push (cNode, answer)) s.resumeStack,
         tableEntries := s.tableEntries.insert key { entry with waiters := entry.waiters.push waiter } }

def getTop : SynthM GeneratorNode := do
  pure (← get).generatorStack.back

@[inline] def modifyTop (f : GeneratorNode → GeneratorNode) : SynthM Unit :=
  modify fun s => { s with generatorStack := s.generatorStack.modify (s.generatorStack.size - 1) f }

/-- Try the next instance in the node on the top of the generator stack. -/
def generate : SynthM Unit := do
  let gNode ← getTop
  if gNode.currInstanceIdx == 0  then
    modify fun s => { s with generatorStack := s.generatorStack.pop }
  else do
    let key  := gNode.key
    let idx  := gNode.currInstanceIdx - 1
    let inst := gNode.instances.get! idx
    let mctx := gNode.mctx
    let mvar := gNode.mvar
    trace[Meta.synthInstance.generate] "instance {inst}"
    modifyTop fun gNode => { gNode with currInstanceIdx := idx }
    match (← tryResolve mctx mvar inst) with
    | none                  => pure ()
    | some (mctx, subgoals) => consume { key := key, mvar := mvar, subgoals := subgoals, mctx := mctx, size := 0 }

def getNextToResume : SynthM (ConsumerNode × Answer) := do
  let s ← get
  let r := s.resumeStack.back
  modify fun s => { s with resumeStack := s.resumeStack.pop }
  pure r

/--
  Given `(cNode, answer)` on the top of the resume stack, continue execution by using `answer` to solve the
  next subgoal. -/
def resume : SynthM Unit := do
  let (cNode, answer) ← getNextToResume
  match cNode.subgoals with
  | []         => panic! "resume found no remaining subgoals"
  | mvar::rest =>
    match (← tryAnswer cNode.mctx mvar answer) with
    | none      => pure ()
    | some mctx =>
      withMCtx mctx <| traceM `Meta.synthInstance.resume do
        let goal    ← inferType cNode.mvar
        let subgoal ← inferType mvar
        pure m!"size: {cNode.size + answer.size}, {goal} <== {subgoal}"
      consume { key := cNode.key, mvar := cNode.mvar, subgoals := rest, mctx := mctx, size := cNode.size + answer.size }

def step : SynthM Bool := do
  checkMaxHeartbeats
  let s ← get
  if !s.resumeStack.isEmpty then
    resume
    pure true
  else if !s.generatorStack.isEmpty then
    generate
    pure true
  else
    pure false

def getResult : SynthM (Option AbstractMVarsResult) := do
  pure (← get).result?

partial def synth : SynthM (Option AbstractMVarsResult) := do
  if (← step) then
    match (← getResult) with
    | none        => synth
    | some result => pure result
  else
    trace[Meta.synthInstance] "failed"
    pure none

def main (type : Expr) (maxResultSize : Nat) : MetaM (Option AbstractMVarsResult) :=
  withCurrHeartbeats <| traceCtx `Meta.synthInstance do
     trace[Meta.synthInstance] "main goal {type}"
     let mvar ← mkFreshExprMVar type
     let mctx ← getMCtx
     let key    := mkTableKey mctx type
     let action : SynthM (Option AbstractMVarsResult) := do
       newSubgoal mctx key mvar Waiter.root
       synth
     action.run { maxResultSize := maxResultSize, maxHeartbeats := getMaxHeartbeats (← getOptions) } |>.run' {}

end SynthInstance

/-
Type class parameters can be annotated with `outParam` annotations.

Given `C a_1 ... a_n`, we replace `a_i` with a fresh metavariable `?m_i` IF
`a_i` is an `outParam`.
The result is type correct because we reject type class declarations IF
it contains a regular parameter X that depends on an `out` parameter Y.

Then, we execute type class resolution as usual.
If it succeeds, and metavariables ?m_i have been assigned, we try to unify
the original type `C a_1 ... a_n` witht the normalized one.
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

private partial def preprocessArgs (type : Expr) (i : Nat) (args : Array Expr) : MetaM (Array Expr) := do
  if h : i < args.size then
    let type ← whnf type
    match type with
    | Expr.forallE _ d b _ => do
      let arg := args.get ⟨i, h⟩
      let arg ← if isOutParam d then mkFreshExprMVar d else pure arg
      let args := args.set ⟨i, h⟩ arg
      preprocessArgs (b.instantiate1 arg) (i+1) args
    | _ =>
      throwError "type class resolution failed, insufficient number of arguments" -- TODO improve error message
  else
    return args

private def preprocessOutParam (type : Expr) : MetaM Expr :=
  forallTelescope type fun xs typeBody => do
    match typeBody.getAppFn with
    | c@(Expr.const constName us _) =>
      let env ← getEnv
      if !hasOutParams env constName then
        return type
      else
        let args := typeBody.getAppArgs
        let cType ← inferType c
        let args ← preprocessArgs cType 0 args
        mkForallFVars xs (mkAppN c args)
    | _ =>
      return type

/-
  Remark: when `maxResultSize? == none`, the configuration option `synthInstance.maxResultSize` is used.
  Remark: we use a different option for controlling the maximum result size for coercions.
-/

def synthInstance? (type : Expr) (maxResultSize? : Option Nat := none) : MetaM (Option Expr) := do profileitM Exception "typeclass inference" (← getOptions) do
  let opts ← getOptions
  let maxResultSize := maxResultSize?.getD (synthInstance.maxSize.get opts)
  let inputConfig ← getConfig
  withConfig (fun config => { config with isDefEqStuckEx := true, transparency := TransparencyMode.instances,
                                          foApprox := true, ctxApprox := true, constApprox := false,
                                          ignoreLevelMVarDepth := true }) do
    let type ← instantiateMVars type
    let type ← preprocess type
    let s ← get
    match s.cache.synthInstance.find? type with
    | some result => pure result
    | none        =>
      let result? ← withNewMCtxDepth do
        let normType ← preprocessOutParam type
        trace[Meta.synthInstance] "preprocess: {type} ==> {normType}"
        SynthInstance.main normType maxResultSize
      let resultHasUnivMVars := if let some result := result? then !result.paramNames.isEmpty else false
      let result? ← match result? with
        | none        => pure none
        | some result => do
          let (_, _, result) ← openAbstractMVarsResult result
          trace[Meta.synthInstance] "result {result}"
          let resultType ← inferType result
          if (← withConfig (fun _ => inputConfig) <| isDefEq type resultType) then
            let result ← instantiateMVars result
            pure (some result)
          else
            trace[Meta.synthInstance] "result type{indentExpr resultType}\nis not definitionally equal to{indentExpr type}"
            pure none
      if type.hasMVar || resultHasUnivMVars then
        pure result?
      else do
        modify fun s => { s with cache := { s.cache with synthInstance := s.cache.synthInstance.insert type result? } }
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
private def synthPendingImp (mvarId : MVarId) : MetaM Bool := withIncRecDepth <| withMVarContext mvarId do
  let mvarDecl ← getMVarDecl mvarId
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
            if (← isExprMVarAssigned mvarId) then
              return false
            else
              assignExprMVar mvarId val
              return true

builtin_initialize
  registerTraceClass `Meta.synthInstance
  registerTraceClass `Meta.synthInstance.globalInstances
  registerTraceClass `Meta.synthInstance.newSubgoal
  registerTraceClass `Meta.synthInstance.tryResolve
  registerTraceClass `Meta.synthInstance.resume
  registerTraceClass `Meta.synthInstance.generate
  registerTraceClass `Meta.synthPending

end Lean.Meta
