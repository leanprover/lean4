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

@[inline] def trace (cls : Name) (mctx : MetavarContext) (msg : Unit → MessageData) : SynthM Unit :=
whenM (MonadTracerAdapter.isTracingEnabledFor cls) $ do
  ctx ← read;
  s   ← get;
  MonadTracerAdapter.addTrace cls (MessageData.context s.env mctx ctx.lctx (msg ()))

@[inline] def liftMeta {α} (x : MetaM α) : SynthM α :=
adaptState (fun (s : State) => (s.toState, s)) (fun s' s => { toState := s', .. s }) x

instance meta2Synth {α} : HasCoe (MetaM α) (SynthM α) := ⟨liftMeta⟩

/-- Return globals and locals instances that may unify with `type` -/
def getInstances (type : Expr) : MetaM (Array Expr) :=
forallTelescopeReducing type $ fun _ type => do
   className? ← isClass type;
   match className? with
   | none   => throwEx $ Exception.notInstance type
   | some className => do
     globalInstances ← getGlobalInstances;
     result ← globalInstances.getUnify type;
     localInstances ← getLocalInstances;
     let result := localInstances.foldl
       (fun (result : Array Expr) linst => if linst.className == className then result.push linst.fvar else result)
       result;
     pure result

/-- Create a new generator node for `mvar` and add `waiter` as its waiter.
    `key` must be `mkTableKey mctx mvarType`. -/
def newSubgoal (key : Expr) (mvar : Expr) (waiter : Waiter) : SynthM Unit :=
do mvarType ← inferType mvar;
   instances ← getInstances mvarType;
   if instances.isEmpty then pure ()
   else do
     mctx ← getMCtx;
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

def wakeUp (answer : Answer) : Waiter → SynthM Unit
| Waiter.root               => modify $ fun s => s -- TODO
| Waiter.consumerNode cNode => modify $ fun s => { resumeStack := s.resumeStack.push (cNode, answer), .. s }

def findEntry (key : Expr) : SynthM (Option TableEntry) :=
do s ← get;
   pure $ s.tableEntries.find key

def getEntry (key : Expr) : SynthM TableEntry :=
do entry? ← findEntry key;
   match entry? with
   | none       => panic! "invalid key at synthInstance"
   | some entry => pure entry

def newAnswer (key : Expr) (answer : Answer) : SynthM Unit :=
do entry ← getEntry key;
   if entry.answers.contains answer then pure ()
   else condM (pure (entry.waiters.any Waiter.isRoot) <||> hasAssignableMVar answer.expr) (pure ()) $
   let newEntry := { answers := entry.answers.push answer, .. entry };
   modify $ fun s => { tableEntries := s.tableEntries.insert key newEntry, .. s };
   entry.waiters.forM (wakeUp answer)

def mkAnswer (cNode : ConsumerNode) : MetaM Answer :=
withMCtx cNode.mctx $ do
  val ← instantiateMVars cNode.mvar;
  abstractMVars val

def mkTableKeyFor (mctx : MetavarContext) (mvar : Expr) : MetaM Expr :=
withMCtx mctx $ do
  mvarType ← inferType mvar;
  pure $ mkTableKey mctx mvarType

def consume (cNode : ConsumerNode) : SynthM Unit :=
match cNode.subgoals with
| [] => do
  answer ← mkAnswer cNode;
  newAnswer cNode.key answer
| mvar::_ => do
   let waiter := Waiter.consumerNode cNode;
   let key := mkTableKey cNode.mctx mvar;
   entry? ← findEntry key;
   match entry? with
   | none       => newSubgoal key mvar waiter
   | some entry => modify $ fun s =>
     { resumeStack  := entry.answers.foldl (fun s answer => s.push (cNode, answer)) s.resumeStack,
       tableEntries := s.tableEntries.insert key { waiters := entry.waiters.push waiter, .. entry },
       .. s }

private partial def mkInstanceTelescopeAux
    (xs : Array Expr) : Array Expr → Nat → List Expr → Expr → Expr → MetaM (List Expr × Expr × Expr)
| mvars, j, subgoals, instVal, Expr.forallE n d b c => do
  let d     := d.instantiateRevRange j mvars.size mvars;
  type ← mkForall xs d;
  mvar ← mkFreshExprMVar type;
  let arg := mkAppN mvar xs;
  let instVal := mkApp instVal arg;
  let subgoals := if c.binderInfo.isInstImplicit then mvar::subgoals else subgoals;
  let mvars    := mvars.push mvar;
  mkInstanceTelescopeAux mvars j subgoals instVal b
| mvars, j, subgoals, instVal, type => do
  let type := type.instantiateRevRange j mvars.size mvars;
  type ← whnf type;
  if type.isForall then
    mkInstanceTelescopeAux mvars mvars.size subgoals instVal type
  else
    pure (subgoals, instVal, type)

def mkInstanceTelescope (xs : Array Expr) (inst : Expr) : MetaM (List Expr × Expr × Expr) :=
do instType ← inferType inst;
   mkInstanceTelescopeAux xs #[] 0 [] inst instType

def tryResolve (mctx : MetavarContext) (mvar : Expr) (inst : Expr) : MetaM (Option (MetavarContext × List Expr)) :=
withMCtx mctx $ do
  mvarType ← inferType mvar;
  forallTelescopeReducing mvarType $ fun xs mvarTypeBody => do
    (subgoals, instVal, instTypeBody) ← mkInstanceTelescope xs inst;
    condM (isDefEq mvarTypeBody instTypeBody)
      (do instVal ← mkLambda xs instVal;
          condM (isDefEq mvar instVal)
            (do mctx ← getMCtx; pure (some (mctx, subgoals)))
            (pure none))
      (pure none)

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
     result? ← tryResolve gNode.mctx gNode.mvar inst;
     match result? with
     | none                  => pure ()
     | some (mctx, subgoals) => consume { key := gNode.key, mvar := gNode.mvar, subgoals := subgoals, mctx := mctx }

def main (type : Expr) : MetaM (Option Expr) :=
do Meta.trace `Meta.synthInstance $ fun _ => type;
   mvar ← mkFreshExprMVar type;
   pure none -- TODO

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

def synthInstance (type : Expr) : MetaM (Option Expr) :=
usingTransparency TransparencyMode.reducible $ do
  type ← instantiateMVars type;
  type ← preprocess type;
  s ← get;
  match s.cache.synthInstance.find type with
  | some result => pure result
  | none        => do
    result ← withNewMCtxDepth $ do {
      (normType, replacements) ← preprocessOutParam type;
      result? ← SynthInstance.main normType;
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
def trySynthInstance (type : Expr) : MetaM (LOption Expr) :=
adaptReader (fun (ctx : Context) => { config := { isDefEqStuckEx := true, .. ctx.config }, .. ctx }) $
  catch
    (toLOptionM $ synthInstance type)
    (fun ex => match ex with
      | Exception.isExprDefEqStuck _ _ _  => pure LOption.undef
      | Exception.isLevelDefEqStuck _ _ _ => pure LOption.undef
      | _                                 => throw ex)

end Meta
end Lean
