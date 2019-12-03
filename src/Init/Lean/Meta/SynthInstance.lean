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

namespace  MkTableKey

structure State :=
(nextLevelIdx : Nat := 0)
(nextExprIdx  : Nat := 0)
(lmap : HashMap MVarId Level := {})
(emap : HashMap MVarId Expr := {})

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
        let u' := mkLevelParam $ mkNameNum `_synthKey s.nextLevelIdx;
        modify $ fun s => { nextLevelIdx := s.nextLevelIdx + 1, lmap := s.lmap.insert mvarId u', .. s };
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
        let e' := mkFVar $ mkNameNum `_synthKey s.nextExprIdx;
        modify $ fun s => { nextExprIdx := s.nextExprIdx + 1, emap := s.emap.insert mvarId e', .. s };
        pure e'
  | _ => pure e

end MkTableKey

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
(mainMVarId     : MVarId)
(nextKeyIdx     : Nat                               := 0)
(generatorStack : Array GeneratorNode               := #[])
(resumeStack    : Array (ConsumerNode × Answer)     := #[])
(tableEntries   : PersistentHashMap Expr TableEntry := {})

abbrev SynthM := ReaderT Context (EStateM Exception State)

instance SynthM.inhabited {α} : Inhabited (SynthM α) := ⟨throw $ Exception.other ""⟩

@[inline] private def getTraceState : SynthM TraceState :=
do s ← get; pure s.traceState

@[inline] private def getOptions : SynthM Options :=
do ctx ← read; pure ctx.config.opts

instance tracer : SimpleMonadTracerAdapter SynthM :=
{ getOptions       := getOptions,
  getTraceState    := getTraceState,
  modifyTraceState := fun f => modify $ fun s => { traceState := f s.traceState, .. s } }

def traceCore (cls : Name) (msg : MessageData) : SynthM Unit :=
do ctx ← read;
   s   ← get;
   MonadTracerAdapter.addTrace cls (MessageData.context s.env s.mctx ctx.lctx msg)

@[inline] def trace (cls : Name) (msg : Unit → MessageData) : SynthM Unit :=
whenM (MonadTracerAdapter.isTracingEnabledFor cls) $ traceCore cls (msg ())

@[inline] def liftMeta {α} (x : MetaM α) : SynthM α :=
adaptState (fun (s : State) => (s.toState, s)) (fun s' s => { toState := s', .. s }) x

instance meta2Synth {α} : HasCoe (MetaM α) (SynthM α) := ⟨liftMeta⟩

@[inline] def withMCtx {α} (mctx : MetavarContext) (x : SynthM α) : SynthM α :=
do mctx' ← getMCtx;
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
     Meta.trace `Meta.synthInstance.globalInstances $ fun _ => type ++ " " ++ result;
     localInstances ← getLocalInstances;
     let result := localInstances.foldl
       (fun (result : Array Expr) linst => if linst.className == className then result.push linst.fvar else result)
       result;
     pure result

/-- Create a new generator node for `mvar` and add `waiter` as its waiter.
    `key` must be `mkTableKey mctx mvarType`. -/
def newSubgoal (mctx : MetavarContext) (key : Expr) (mvar : Expr) (waiter : Waiter) : SynthM Unit :=
withMCtx mctx $ do
  trace `Meta.synthInstance.newSubgoal $ fun _ => key;
  mvarType  ← inferType mvar;
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

def findEntry (key : Expr) : SynthM (Option TableEntry) :=
do s ← get;
   pure $ s.tableEntries.find key

def getEntry (key : Expr) : SynthM TableEntry :=
do entry? ← findEntry key;
   match entry? with
   | none       => panic! "invalid key at synthInstance"
   | some entry => pure entry

def mkTableKeyFor (mctx : MetavarContext) (mvar : Expr) : SynthM Expr :=
withMCtx mctx $ do
  mvarType ← inferType mvar;
  mvarType ← instantiateMVars mvarType;
  pure $ mkTableKey mctx mvarType

/- Remark: `(lctx, localInsts)` is the local context before we created the telescope containing `xs`.
   We must use `(lctx, localInsts)` to create the new fresh metavariables `mvar`, otherwise the
   application `mvar xs` is not a higher order pattern. -/
private partial def mkInstanceTelescopeAux (lctx : LocalContext) (localInsts : LocalInstances) (xs : Array Expr)
    : Array Expr → Nat → List Expr → Expr → Expr → MetaM (List Expr × Expr × Expr)
| subst, j, subgoals, instVal, Expr.forallE n d b c => do
  let d     := d.instantiateRevRange j subst.size subst;
  type ← mkForall xs d;
  mvar ← mkFreshExprMVarAt lctx localInsts type;
  let arg := mkAppN mvar xs;
  let instVal := mkApp instVal arg;
  let subgoals := if c.binderInfo.isInstImplicit then mvar::subgoals else subgoals;
  let subst    := subst.push (mkAppN mvar xs);
  mkInstanceTelescopeAux subst j subgoals instVal b
| subst, j, subgoals, instVal, type => do
  let type := type.instantiateRevRange j subst.size subst;
  type ← whnf type;
  if type.isForall then
    mkInstanceTelescopeAux subst subst.size subgoals instVal type
  else
    pure (subgoals, instVal, type)

def mkInstanceTelescope (lctx : LocalContext) (localInsts : LocalInstances) (xs : Array Expr) (inst : Expr) : MetaM (List Expr × Expr × Expr) :=
do instType ← inferType inst;
   mkInstanceTelescopeAux lctx localInsts xs #[] 0 [] inst instType

def tryResolveCore (mvar : Expr) (inst : Expr) : MetaM (Option (MetavarContext × List Expr)) :=
do mvarType   ← inferType mvar;
   lctx       ← getLCtx;
   localInsts ← getLocalInstances;
   forallTelescopeReducing mvarType $ fun xs mvarTypeBody => do
     (subgoals, instVal, instTypeBody) ← mkInstanceTelescope lctx localInsts xs inst;
     Meta.trace `Meta.synthInstance.tryResolve $ fun _ => mvarTypeBody ++ " =?= " ++ instTypeBody;
     condM (isDefEq mvarTypeBody instTypeBody)
       (do instVal ← mkLambda xs instVal;
           condM (isDefEq mvar instVal)
             (do Meta.trace `Meta.synthInstance.tryResolve $ fun _ => fmt "success";
                 mctx ← getMCtx;
                 pure (some (mctx, subgoals)))
             (do Meta.trace `Meta.synthInstance.tryResolve $ fun _ => fmt "failure assigning";
                 pure none))
       (do Meta.trace `Meta.synthInstance.tryResolve $ fun _ => fmt "failure";
           pure none)

def tryResolve (mctx : MetavarContext) (mvar : Expr) (inst : Expr) : SynthM (Option (MetavarContext × List Expr)) :=
withMCtx mctx $ tryResolveCore mvar inst

def tryAnswer (mctx : MetavarContext) (mvar : Expr) (answer : Answer) : SynthM (Option (MetavarContext × List Expr)) :=
withMCtx mctx $ do
  (_, _, val) ← openAbstractMVarsResult answer;
  tryResolveCore mvar val

def wakeUp (answer : Answer) : Waiter → SynthM Unit
| Waiter.root               =>
  if answer.paramNames.isEmpty && answer.numMVars == 0 then do
    s ← get;
    let mvar := s.mainMVarId;
    condM (isDefEq (mkMVar mvar) answer.expr)
      (pure ())
      (do trace `Meta.synthInstance $ fun _ => "fail to assign main metavariable " ++ answer.expr;
          pure ())
  else do
    (_, _, answerExpr) ← openAbstractMVarsResult answer;
    trace `Meta.synthInstance $ fun _ => "answer contains metavariables " ++ answerExpr;
    pure ()
| Waiter.consumerNode cNode => modify $ fun s => { resumeStack := s.resumeStack.push (cNode, answer), .. s }

def newAnswer (key : Expr) (answer : Answer) : SynthM Unit :=
do entry ← getEntry key;
   if entry.answers.contains answer then pure ()
   else if entry.waiters.any Waiter.isRoot then pure ()
   else
     let newEntry := { answers := entry.answers.push answer, .. entry };
     modify $ fun s => { tableEntries := s.tableEntries.insert key newEntry, .. s };
     entry.waiters.forM (wakeUp answer)

def mkAnswer (cNode : ConsumerNode) : SynthM Answer :=
withMCtx cNode.mctx $ do
  val ← instantiateMVars cNode.mvar;
  abstractMVars val

def consume (cNode : ConsumerNode) : SynthM Unit :=
match cNode.subgoals with
| [] => do
  answer ← mkAnswer cNode;
  newAnswer cNode.key answer
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

def getTop : SynthM GeneratorNode :=
do s ← get;
   pure s.generatorStack.back

@[inline] def modifyTop (f : GeneratorNode → GeneratorNode) : SynthM Unit :=
modify $ fun s => { generatorStack := s.generatorStack.modify (s.generatorStack.size - 1) f, .. s }

def generate : SynthM Unit :=
do gNode ← getTop;
   if gNode.currInstanceIdx == 0  then
     modify $ fun s => { generatorStack := s.generatorStack.pop, .. s }
   else do
     let idx  := gNode.currInstanceIdx - 1;
     modifyTop $ fun gNode => { currInstanceIdx := idx, .. gNode };
     let inst := gNode.instances.get! idx;
     trace `Meta.synthInstance $ fun _ => "try instance " ++ inst;
     result? ← tryResolve gNode.mctx gNode.mvar inst;
     match result? with
     | none                  => pure ()
     | some (mctx, subgoals) => consume { key := gNode.key, mvar := gNode.mvar, subgoals := subgoals, mctx := mctx }

def getNextToResume : SynthM (ConsumerNode × Answer) :=
do s ← get;
   let r := s.resumeStack.back;
   modify $ fun s => { resumeStack := s.resumeStack.pop, .. s };
   pure r

def resume : SynthM Unit :=
do (cNode, answer) ← getNextToResume;
   match cNode.subgoals with
   | []         => panic! "resume found no remaining subgoals"
   | mvar::rest => do
     result? ← tryAnswer cNode.mctx mvar answer;
     match result? with
     | none                  => pure ()
     | some (mctx, subgoals) => consume { key := cNode.key, mvar := cNode.mvar, subgoals := subgoals ++ rest, mctx := mctx }

def step : SynthM Bool :=
do s ← get;
   if !s.resumeStack.isEmpty then do resume; pure true
   else if !s.generatorStack.isEmpty then do generate; pure true
   else pure false

partial def synth : Nat → SynthM (Option Expr)
| 0   => do
  trace `Meta.synthInstance $ fun _ => fmt "synthInstance is out of fule";
  pure none
| n+1 => do
  condM step
    (do s ← get;
        val? ← getExprMVarAssignment s.mainMVarId;
        match val? with
        | none     => synth n
        | some val => do
          val ← instantiateMVars val;
          pure (some val))
    (do trace `Meta.synthInstance $ fun _ => fmt "failed";
        pure none)

def main (type : Expr) (fuel : Nat) : MetaM (Option Expr) :=
traceCtx `Meta.synthInstance $ do
   Meta.trace `Meta.synthInstance $ fun _ => "main goal " ++ type;
   mvar ← mkFreshExprMVar type;
   mctx ← getMCtx;
   let key := mkTableKey mctx type;
   adaptState' (fun (s : Meta.State) => { State . mainMVarId := mvar.mvarId!, .. s }) (fun (s : State) => s.toState) $ do
     newSubgoal mctx key mvar Waiter.root;
     synth fuel

end SynthInstance

structure Replacements :=
(levelReplacements : Array (Level × Level) := #[])
(exprReplacements : Array (Expr × Expr)    := #[])

private def preprocess (type : Expr) : MetaM Expr :=
forallTelescopeReducing type $ fun xs type => do
  type ← whnf type;
  mkForall xs type

private def preprocessLevels (us : List Level) : MetaM (List Level × Array (Level × Level)) :=
do (us, r) ← us.foldlM
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

def synthInstance (type : Expr) (fuel : Nat := 10000) : MetaM (Option Expr) :=
usingTransparency TransparencyMode.reducible $ do
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
    if type.hasMVar then do
      modify $ fun s => { cache := { synthInstance := s.cache.synthInstance.insert type result, .. s.cache }, .. s };
      pure result
    else
      pure result

/--
  Return `LOption.some r` if succeeded, `LOption.none` if it failed, and `LOption.undef` if
  instance cannot be synthesized right now because `type` contains metavariables. -/
def trySynthInstance (type : Expr) (fuel : Nat := 10000) : MetaM (LOption Expr) :=
adaptReader (fun (ctx : Context) => { config := { isDefEqStuckEx := true, .. ctx.config }, .. ctx }) $
  catch
    (toLOptionM $ synthInstance type fuel)
    (fun ex => match ex with
      | Exception.isExprDefEqStuck _ _ _  => pure LOption.undef
      | Exception.isLevelDefEqStuck _ _ _ => pure LOption.undef
      | _                                 => throw ex)

end Meta
end Lean
