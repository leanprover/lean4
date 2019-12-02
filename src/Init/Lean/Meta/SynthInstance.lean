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

structure Context extends Meta.Context :=
(globalInstances : DiscrTree Expr := {})

structure GeneratorNode :=
(mctx            : MetavarContext)
(instances       : Array Expr)
(currInstanceIdx : Nat)

structure ConsumerNode :=
(mctx     : MetavarContext)
(subgoals : List Expr)
(answer   : MVarId)

inductive Waiter
| consumerNode : ConsumerNode → Waiter
| root         : Waiter

/-
We represent the tabled/cached entries using

1- An imperfect discrimination tree that stores the type class instances (i.e., types)
   an unique index.

2- A persistent array which represents a map from unique indices to `TableEntry`.
-/

structure Key :=
(key : AbstractMVarsResult)
(idx : Nat)

structure TableEntry :=
(waiters : Array Waiter)
(answers : Array AbstractMVarsResult)

/-
  Remark: the SynthInstance.State is not really an extension of `Meta.State`.
  The field `postponed` is not needed, and the field `mctx` is misleading since
  `synthInstance` methods operate over different `MetavarContext`s simultaneously.
  That being said, we still use `extends` because it makes it simpler to move from
  `M` to `MetaM`.
-/
structure State extends Meta.State :=
(mainMVarId     : MVarId)
(generatorStack : Array GeneratorNode         := #[])
(resumeStack    : Array (ConsumerNode × Expr) := #[])
(tableKeys      : DiscrTree Key               := {})
(tableEntries   : PersistentArray TableEntry  := {})

abbrev SynthM := ReaderT Context (EStateM Exception State)

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

@[inline] def runMetaM {α} (x : MetaM α) : SynthM α :=
fun ctx => adaptState (fun (s : State) => (s.toState, s)) (fun s' s => { toState := s', .. s }) (x ctx.toContext)

def main (type : Expr) : MetaM (Option Expr) :=
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
      trace `Meta.synthInstance $ fun _ => normType;
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
