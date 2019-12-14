/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Selsam, Leonardo de Moura

Type class instance synthesizer using tabled resolution.
-/
import Init.Lean.Meta.Basic
import Init.Lean.Meta.Instances
import Init.Lean.Meta.LevelDefEq
import Init.Lean.Meta.AbstractMVars

namespace Lean
namespace Meta
namespace SynthInstance

structure GeneratorNode :=
(mvar            : Expr)
(key             : Expr)
(mctx            : MetavarContext)
(instances       : Array Expr)
(currInstanceIdx : Nat)

instance GeneratorNode.inhabited : Inhabited GeneratorNode := ⟨⟨arbitrary _, arbitrary _, arbitrary _, arbitrary _, 0⟩⟩

structure ConsumerNode :=
(mvar     : Expr)
(key      : Expr)
(mctx     : MetavarContext)
(subgoals : List Expr)

instance Consumernode.inhabited : Inhabited ConsumerNode := ⟨⟨arbitrary _, arbitrary _, arbitrary _, []⟩⟩

inductive Waiter
| consumerNode : ConsumerNode → Waiter
| root         : Waiter

def Waiter.isRoot : Waiter → Bool
| Waiter.consumerNode _ => false
| Waiter.root           => true

/-
  In tabled resolution, we creating a mapping from goals (e.g., `HasCoe Nat ?x`) to
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

structure State :=
(nextIdx : Nat := 0)
(lmap    : HashMap MVarId Level := {})
(emap    : HashMap MVarId Expr := {})

abbrev M := ReaderT MetavarContext (StateM State)

partial def normLevel : Level → M Level
| u => if !u.hasMVar then pure u else
  match u with
  | Level.succ v _      => do v ← normLevel v; pure $ u.updateSucc! v
  | Level.max v w _     => do v ← normLevel v; w ← normLevel w; pure $ u.updateMax! v w
  | Level.imax v w _    => do v ← normLevel v; w ← normLevel w; pure $ u.updateIMax! v w
  | Level.mvar mvarId _ => do
    mctx ← read;
    if !mctx.isLevelAssignable mvarId then pure u
    else do
      s ← get;
      match s.lmap.find mvarId with
      | some u' => pure u'
      | none    => do
        let u' := mkLevelParam $ mkNameNum `_tc s.nextIdx;
        modify $ fun s => { nextIdx := s.nextIdx + 1, lmap := s.lmap.insert mvarId u', .. s };
        pure u'
  | u                   => pure u

partial def normExpr : Expr → M Expr
| e => if !e.hasMVar then pure e else
  match e with
  | Expr.const _ us _    => do us ← us.mapM normLevel; pure $ e.updateConst! us
  | Expr.sort u _        => do u ← normLevel u; pure $ e.updateSort! u
  | Expr.app f a _       => do f ← normExpr f; a ← normExpr a; pure $ e.updateApp! f a
  | Expr.letE _ t v b _  => do t ← normExpr t; v ← normExpr v; b ← normExpr b; pure $ e.updateLet! t v b
  | Expr.forallE _ d b _ => do d ← normExpr d; b ← normExpr b; pure $ e.updateForallE! d b
  | Expr.lam _ d b _     => do d ← normExpr d; b ← normExpr b; pure $ e.updateLambdaE! d b
  | Expr.mdata _ b _     => do b ← normExpr b; pure $ e.updateMData! b
  | Expr.proj _ _ b _    => do b ← normExpr b; pure $ e.updateProj! b
  | Expr.mvar mvarId _   => do
    mctx ← read;
    if !mctx.isExprAssignable mvarId then pure e
    else do
      s ← get;
      match s.emap.find mvarId with
      | some e' => pure e'
      | none    => do
        let e' := mkFVar $ mkNameNum `_tc s.nextIdx;
        modify $ fun s => { nextIdx := s.nextIdx + 1, emap := s.emap.insert mvarId e', .. s };
        pure e'
  | _ => pure e

end MkTableKey

/- Remark: `mkTableKey` assumes `e` does not contain assigned metavariables. -/
def mkTableKey (mctx : MetavarContext) (e : Expr) : Expr :=
(MkTableKey.normExpr e mctx).run' {}

abbrev Answer := AbstractMVarsResult

structure TableEntry :=
(waiters : Array Waiter)
(answers : Array Answer := #[])

/-
  Remark: the SynthInstance.State is not really an extension of `Meta.State`.
  The field `postponed` is not needed, and the field `mctx` is misleading since
  `synthInstance` methods operate over different `MetavarContext`s simultaneously.
  That being said, we still use `extends` because it makes it simpler to move from
  `M` to `MetaM`.
-/
structure State extends Meta.State :=
(result         : Option Expr                   := none)
(generatorStack : Array GeneratorNode           := #[])
(resumeStack    : Array (ConsumerNode × Answer) := #[])
(tableEntries   : HashMap Expr TableEntry       := {})

abbrev SynthM := ReaderT Context (EStateM Exception State)

instance SynthM.inhabited {α} : Inhabited (SynthM α) := ⟨throw $ Exception.other ""⟩

def getTraceState : SynthM TraceState := do s ← get; pure s.traceState
def getOptions : SynthM Options := do ctx ← read; pure ctx.config.opts
def addContext (msg : MessageData) : SynthM MessageData := do
ctx ← read;
s   ← get;
pure $ MessageData.context s.env s.mctx ctx.lctx msg

instance tracer : SimpleMonadTracerAdapter SynthM :=
{ getOptions       := getOptions,
  getTraceState    := getTraceState,
  addContext       := addContext,
  modifyTraceState := fun f => modify $ fun s => { traceState := f s.traceState, .. s } }

@[inline] def liftMeta {α} (x : MetaM α) : SynthM α :=
adaptState (fun (s : State) => (s.toState, s)) (fun s' s => { toState := s', .. s }) x

instance meta2Synth {α} : HasCoe (MetaM α) (SynthM α) := ⟨liftMeta⟩

@[inline] def withMCtx {α} (mctx : MetavarContext) (x : SynthM α) : SynthM α := do
mctx' ← getMCtx;
modify $ fun s => { mctx := mctx, .. s };
finally x (modify $ fun s => { mctx := mctx', .. s })

/-- Return globals and locals instances that may unify with `type` -/
def getInstances (type : Expr) : MetaM (Array Expr) :=
forallTelescopeReducing type $ fun _ type => do
  className? ← isClass type;
  match className? with
  | none   => throwEx $ Exception.notInstance type
  | some className => do
    globalInstances ← getGlobalInstances;
    result ← globalInstances.getUnify type;
    result ← result.mapM $ fun c => match c with
      | Expr.const constName us _ => do us ← us.mapM (fun _ => mkFreshLevelMVar); pure $ c.updateConst! us
      | _ => panic! "global instance is not a constant";
    trace! `Meta.synthInstance.globalInstances (type ++ " " ++ result);
    localInstances ← getLocalInstances;
    let result := localInstances.foldl
      (fun (result : Array Expr) linst => if linst.className == className then result.push linst.fvar else result)
      result;
    pure result

/-- Create a new generator node for `mvar` and add `waiter` as its waiter.
    `key` must be `mkTableKey mctx mvarType`. -/
def newSubgoal (mctx : MetavarContext) (key : Expr) (mvar : Expr) (waiter : Waiter) : SynthM Unit :=
withMCtx mctx $ do
  trace! `Meta.synthInstance.newSubgoal key;
  mvarType  ← inferType mvar;
  mvarType  ← instantiateMVars mvarType;
  instances ← getInstances mvarType;
  mctx      ← getMCtx;
  if instances.isEmpty then pure ()
  else do
    let node : GeneratorNode := {
      mvar            := mvar,
      key             := key,
      mctx            := mctx,
      instances       := instances,
      currInstanceIdx := instances.size
    };
    let entry : TableEntry := { waiters := #[waiter] };
    modify $ fun s =>
     { generatorStack := s.generatorStack.push node,
       tableEntries   := s.tableEntries.insert key entry,
       .. s }

def findEntry (key : Expr) : SynthM (Option TableEntry) := do
s ← get;
pure $ s.tableEntries.find key

def getEntry (key : Expr) : SynthM TableEntry := do
entry? ← findEntry key;
match entry? with
| none       => panic! "invalid key at synthInstance"
| some entry => pure entry

/--
  Create a `key` for the goal associated with the given metavariable.
  That is, we create a key for the type of the metavariable.

  We must instantiate assigned metavariables before we invoke `mkTableKey`. -/
def mkTableKeyFor (mctx : MetavarContext) (mvar : Expr) : SynthM Expr :=
withMCtx mctx $ do
  mvarType ← inferType mvar;
  mvarType ← instantiateMVars mvarType;
  pure $ mkTableKey mctx mvarType

/- See `getSubgoals`

   We use the parameter `j` to reduce the number of `instantiate*` invocations.
   It is the same approach we use at `forallTelescope` and `lambdaTelescope`.
   Given `getSubgoalsAux args j subgoals instVal type`,
   we have that `type.instantiateRevRange j args.size args` does not have loose bound variables. -/
private partial def getSubgoalsAux (lctx : LocalContext) (localInsts : LocalInstances) (xs : Array Expr)
    : Array Expr → Nat → List Expr → Expr → Expr → MetaM (List Expr × Expr × Expr)
| args, j, subgoals, instVal, Expr.forallE n d b c => do
  let d        := d.instantiateRevRange j args.size args;
  mvarType ← mkForall xs d;
  mvar     ← mkFreshExprMVarAt lctx localInsts mvarType;
  let arg      := mkAppN mvar xs;
  let instVal  := mkApp instVal arg;
  let subgoals := if c.binderInfo.isInstImplicit then mvar::subgoals else subgoals;
  let args     := args.push (mkAppN mvar xs);
  getSubgoalsAux args j subgoals instVal b
| args, j, subgoals, instVal, type => do
  let type := type.instantiateRevRange j args.size args;
  type ← whnf type;
  if type.isForall then
    getSubgoalsAux args args.size subgoals instVal type
  else
    pure (subgoals, instVal, type)

/--
  `getSubgoals lctx localInsts xs inst` creates the subgoals for the instantiate `inst`.
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
def getSubgoals (lctx : LocalContext) (localInsts : LocalInstances) (xs : Array Expr) (inst : Expr) : MetaM (List Expr × Expr × Expr) := do
instType ← inferType inst;
getSubgoalsAux lctx localInsts xs #[] 0 [] inst instType

def tryResolveCore (mvar : Expr) (inst : Expr) : MetaM (Option (MetavarContext × List Expr)) := do
mvarType   ← inferType mvar;
lctx       ← getLCtx;
localInsts ← getLocalInstances;
forallTelescopeReducing mvarType $ fun xs mvarTypeBody => do
  (subgoals, instVal, instTypeBody) ← getSubgoals lctx localInsts xs inst;
  trace! `Meta.synthInstance.tryResolve (mvarTypeBody ++ " =?= " ++ instTypeBody);
  condM (isDefEq mvarTypeBody instTypeBody)
    (do instVal ← mkLambda xs instVal;
        condM (isDefEq mvar instVal)
          (do trace! `Meta.synthInstance.tryResolve "success";
              mctx ← getMCtx;
              pure (some (mctx, subgoals)))
          (do trace! `Meta.synthInstance.tryResolve "failure assigning";
              pure none))
    (do trace! `Meta.synthInstance.tryResolve "failure";
        pure none)

/--
  Try to synthesize metavariable `mvar` using the instance `inst`.
  Remark: `mctx` contains `mvar`.
  If it succeeds, the result it a new updated metavariable context and a new list of subgoals.
  A subgoal is created for each instance implicit parameter of `inst`. -/
def tryResolve (mctx : MetavarContext) (mvar : Expr) (inst : Expr) : SynthM (Option (MetavarContext × List Expr)) :=
traceCtx `Meta.synthInstance.tryResolve $ withMCtx mctx $ tryResolveCore mvar inst

/--
  Assign a precomputed answer to `mvar`.
  If it succeeds, the result it a new updated metavariable context and a new list of subgoals. -/
def tryAnswer (mctx : MetavarContext) (mvar : Expr) (answer : Answer) : SynthM (Option MetavarContext) :=
withMCtx mctx $ do
  (_, _, val) ← openAbstractMVarsResult answer;
  condM (isDefEq mvar val)
    (do mctx ← getMCtx; pure $ some mctx)
    (pure none)

/-- Move waiters that are waiting for the given answer to the resume stack. -/
def wakeUp (answer : Answer) : Waiter → SynthM Unit
| Waiter.root               =>
  if answer.paramNames.isEmpty && answer.numMVars == 0 then do
    modify $ fun s => { result := answer.expr, .. s }
  else do
    (_, _, answerExpr) ← openAbstractMVarsResult answer;
    trace! `Meta.synthInstance ("skip answer containing metavariables " ++ answerExpr);
    pure ()
| Waiter.consumerNode cNode => modify $ fun s => { resumeStack := s.resumeStack.push (cNode, answer), .. s }

/--
  Create a new answer after `cNode` resolved all subgoals.
  That is, `cNode.subgoals == []`.
  And then, store it in the tabled entries map, and wakeup waiters. -/
def addAnswer (cNode : ConsumerNode) : SynthM Unit := do
answer ← withMCtx cNode.mctx $ do {
  traceM `Meta.synthInstance.newAnswer $ do { mvarType ← inferType cNode.mvar; pure mvarType };
  val ← instantiateMVars cNode.mvar;
  abstractMVars val -- assignable metavariables become parameters
};
-- Remark: `answer` does not contain assignable or assigned metavariables.
let key := cNode.key;
entry ← getEntry key;
if entry.answers.contains answer then pure () -- if answer was already found, then do nothing
else
  let newEntry := { answers := entry.answers.push answer, .. entry };
  modify $ fun s => { tableEntries := s.tableEntries.insert key newEntry, .. s };
  entry.waiters.forM (wakeUp answer)

/-- Process the next subgoal in the given consumer node. -/
def consume (cNode : ConsumerNode) : SynthM Unit :=
match cNode.subgoals with
| []      => addAnswer cNode
| mvar::_ => do
   let waiter := Waiter.consumerNode cNode;
   key ← mkTableKeyFor cNode.mctx mvar;
   entry? ← findEntry key;
   match entry? with
   | none       => newSubgoal cNode.mctx key mvar waiter
   | some entry => modify $ fun s =>
     { resumeStack  := entry.answers.foldl (fun s answer => s.push (cNode, answer)) s.resumeStack,
       tableEntries := s.tableEntries.insert key { waiters := entry.waiters.push waiter, .. entry },
       .. s }

def getTop : SynthM GeneratorNode := do
s ← get; pure s.generatorStack.back

@[inline] def modifyTop (f : GeneratorNode → GeneratorNode) : SynthM Unit :=
modify $ fun s => { generatorStack := s.generatorStack.modify (s.generatorStack.size - 1) f, .. s }

/-- Try the next instance in the node on the top of the generator stack. -/
def generate : SynthM Unit := do
gNode ← getTop;
if gNode.currInstanceIdx == 0  then
  modify $ fun s => { generatorStack := s.generatorStack.pop, .. s }
else do
  let key  := gNode.key;
  let idx  := gNode.currInstanceIdx - 1;
  let inst := gNode.instances.get! idx;
  let mctx := gNode.mctx;
  let mvar := gNode.mvar;
  trace! `Meta.synthInstance.generate ("instance " ++ inst);
  modifyTop $ fun gNode => { currInstanceIdx := idx, .. gNode };
  result? ← tryResolve mctx mvar inst;
  match result? with
  | none                  => pure ()
  | some (mctx, subgoals) => consume { key := key, mvar := mvar, subgoals := subgoals, mctx := mctx }

def getNextToResume : SynthM (ConsumerNode × Answer) := do
s ← get;
let r := s.resumeStack.back;
modify $ fun s => { resumeStack := s.resumeStack.pop, .. s };
pure r

/--
  Given `(cNode, answer)` on the top of the resume stack, continue execution by using `answer` to solve the
  next subgoal. -/
def resume : SynthM Unit := do
(cNode, answer) ← getNextToResume;
match cNode.subgoals with
| []         => panic! "resume found no remaining subgoals"
| mvar::rest => do
  result? ← tryAnswer cNode.mctx mvar answer;
  match result? with
  | none      => pure ()
  | some mctx => do
    withMCtx mctx $ traceM `Meta.synthInstance.resume $ do {
      goal    ← inferType cNode.mvar;
      subgoal ← inferType mvar;
      pure (goal ++ " <== " ++ subgoal)
    };
    consume { key := cNode.key, mvar := cNode.mvar, subgoals := rest, mctx := mctx }

def step : SynthM Bool := do
s ← get;
if !s.resumeStack.isEmpty then do resume; pure true
else if !s.generatorStack.isEmpty then do generate; pure true
else pure false

def getResult : SynthM (Option Expr) := do
s ← get; pure s.result

partial def synth : Nat → SynthM (Option Expr)
| 0   => do
  trace! `Meta.synthInstance "synthInstance is out of fule";
  pure none
| n+1 => do
  condM step
    (do result? ← getResult;
        match result? with
        | none        => synth n
        | some result => pure result)
    (do trace! `Meta.synthInstance "failed";
        pure none)

def main (type : Expr) (fuel : Nat) : MetaM (Option Expr) :=
traceCtx `Meta.synthInstance $ do
   trace! `Meta.synthInstance ("main goal " ++ type);
   mvar ← mkFreshExprMVar type;
   mctx ← getMCtx;
   let key := mkTableKey mctx type;
   adaptState' (fun (s : Meta.State) => { State . .. s }) (fun (s : State) => s.toState) $ do {
     newSubgoal mctx key mvar Waiter.root;
     synth fuel
   }

end SynthInstance

/-
Type class parameters can be annotated with `outParam` annotations.

Given `C a_1 ... a_n`, we replace `a_i` with a fresh metavariable `?m_i` IF
`a_i` is an `outParam`.
The result is type correct because we reject type class declarations IF
it contains a regular parameter X that depends on an `out` parameter Y.

Then, we execute type class resolution as usual.
If it succeeds, and metavariables ?m_i have been assigned, we solve the unification
constraints ?m_i =?= a_i. If we succeed, we return the result. Otherwise, we fail.
These pending unification constraints are stored in the `Replacements` structure.
-/

structure Replacements :=
(levelReplacements : Array (Level × Level) := #[])
(exprReplacements : Array (Expr × Expr)    := #[])

private def preprocess (type : Expr) : MetaM Expr :=
forallTelescopeReducing type $ fun xs type => do
  type ← whnf type;
  mkForall xs type

private def preprocessLevels (us : List Level) : MetaM (List Level × Array (Level × Level)) := do
(us, r) ← us.foldlM
  (fun (r : List Level × Array (Level × Level)) (u : Level) => do
    u ← instantiateLevelMVars u;
    if u.hasMVar then do
      u' ← mkFreshLevelMVar;
      pure (u'::r.1, r.2.push (u, u'))
    else
      pure (u::r.1, r.2))
  ([], #[]);
pure (us.reverse, r)

private partial def preprocessArgs (ys : Array Expr) : Nat → Array Expr → Array (Expr × Expr) → MetaM (Array Expr × Array (Expr × Expr))
| i, args, r => do
  if h : i < ys.size then do
    let y := ys.get ⟨i, h⟩;
    yType ← inferType y;
    if isOutParam yType then do
      if h : i < args.size then do
        let arg := args.get ⟨i, h⟩;
        arg' ← mkFreshExprMVar yType;
        preprocessArgs (i+1) (args.set ⟨i, h⟩ arg') (r.push (arg, arg'))
      else
        throw $ Exception.other "type class resolution failed, insufficient number of arguments" -- TODO improve error message
    else
      preprocessArgs (i+1) args r
  else
    pure (args, r)

private def preprocessOutParam (type : Expr) : MetaM (Expr × Replacements) :=
forallTelescope type $ fun xs typeBody =>
  match typeBody.getAppFn with
  | c@(Expr.const constName us _) => do
    env ← getEnv;
    if !hasOutParams env constName then pure (type, {})
    else do
      let args := typeBody.getAppArgs;
      cType ← inferType c;
      forallTelescopeReducing cType $ fun ys _ => do
        (us, levelReplacements)  ← preprocessLevels us;
        (args, exprReplacements) ← preprocessArgs ys 0 args #[];
        type ← mkForall xs (mkAppN (mkConst constName us) args);
        pure (type, { levelReplacements := levelReplacements, exprReplacements := exprReplacements })
  | _ => pure (type, {})

private def resolveReplacements (r : Replacements) : MetaM Bool :=
try $
  r.levelReplacements.allM (fun ⟨u, u'⟩ => isLevelDefEqAux u u')
  <&&>
  r.exprReplacements.allM (fun ⟨e, e'⟩ => isExprDefEqAux e e')

def synthInstance? (type : Expr) (fuel : Nat := 10000) : MetaM (Option Expr) :=
withConfig (fun config => { transparency := TransparencyMode.reducible, foApprox := true, ctxApprox := true, .. config }) $ do
  type ← instantiateMVars type;
  type ← preprocess type;
  s ← get;
  match s.cache.synthInstance.find type with
  | some result => pure result
  | none        => do
    result ← withNewMCtxDepth $ do {
      (normType, replacements) ← preprocessOutParam type;
      result? ← SynthInstance.main normType fuel;
      match result? with
      | none        => pure none
      | some result => do
        condM (resolveReplacements replacements)
          (do result ← instantiateMVars result;
              condM (hasAssignableMVar result)
                (pure none)
                (pure (some result)))
          (pure none)
    };
    if type.hasMVar then
      pure result
    else do
      modify $ fun s => { cache := { synthInstance := s.cache.synthInstance.insert type result, .. s.cache }, .. s };
      pure result

/--
  Return `LOption.some r` if succeeded, `LOption.none` if it failed, and `LOption.undef` if
  instance cannot be synthesized right now because `type` contains metavariables. -/
def trySynthInstance (type : Expr) (fuel : Nat := 10000) : MetaM (LOption Expr) :=
adaptReader (fun (ctx : Context) => { config := { isDefEqStuckEx := true, .. ctx.config }, .. ctx }) $
  catch
    (toLOptionM $ synthInstance? type fuel)
    (fun ex => match ex with
      | Exception.isExprDefEqStuck _ _ _  => pure LOption.undef
      | Exception.isLevelDefEqStuck _ _ _ => pure LOption.undef
      | _                                 => throw ex)

def synthInstance (type : Expr) (fuel : Nat := 10000) : MetaM Expr := do
result? ← synthInstance? type fuel;
match result? with
| some result => pure result
| none        => throwEx $ Exception.synthInstance type

@[init] private def regTraceClasses : IO Unit := do
registerTraceClass `Meta.synthInstance;
registerTraceClass `Meta.synthInstance.globalInstances;
registerTraceClass `Meta.synthInstance.newSubgoal;
registerTraceClass `Meta.synthInstance.tryResolve;
registerTraceClass `Meta.synthInstance.resume;
registerTraceClass `Meta.synthInstance.generate

end Meta
end Lean
