/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Sebastian Ullrich
-/
import Lean.Util.CollectMVars
import Lean.Meta.Tactic.Assumption
import Lean.Meta.Tactic.Intro
import Lean.Meta.Tactic.Clear
import Lean.Meta.Tactic.Revert
import Lean.Meta.Tactic.Subst
import Lean.Elab.Util
import Lean.Elab.Term

namespace Lean
namespace Elab

def goalsToMessageData (goals : List MVarId) : MessageData :=
MessageData.joinSep (goals.map $ MessageData.ofGoal) (Format.line ++ Format.line)

def Term.reportUnsolvedGoals (goals : List MVarId) : TermElabM Unit := do
ref ← getRef;
let tailRef := ref.getTailWithPos.getD ref;
Term.throwErrorAt tailRef $ "unsolved goals" ++ Format.line ++ goalsToMessageData goals

namespace Tactic

structure Context :=
(main : MVarId)

structure State :=
(goals : List MVarId)

instance State.inhabited : Inhabited State := ⟨{ goals := [] }⟩

structure BacktrackableState :=
(env   : Environment)
(mctx  : MetavarContext)
(goals : List MVarId)

abbrev Exception := Elab.Exception

abbrev TacticM := ReaderT Context $ StateRefT State $ Term.ETermElabM Exception
abbrev Tactic  := Syntax → TacticM Unit

def getEnv : TacticM Environment := do s ← getThe Core.State; pure s.env
def getMCtx : TacticM MetavarContext := do s ← getThe Meta.State; pure s.mctx
def getLCtx : TacticM LocalContext := do ctx ← readThe Meta.Context; pure ctx.lctx
def getLocalInsts : TacticM LocalInstances := do ctx ← readThe Meta.Context; pure ctx.localInstances
def getOptions : TacticM Options := do ctx ← readThe Core.Context; pure ctx.options
def getMVarDecl (mvarId : MVarId) : TacticM MetavarDecl := do mctx ← getMCtx; pure $ mctx.getDecl mvarId

def setEnv (env : Environment) : TacticM Unit := modifyThe Core.State fun s => { s with env := env }
def setMCtx (mctx : MetavarContext) : TacticM Unit := modifyThe Meta.State fun s => { s with mctx := mctx }

@[inline] def modifyMCtx (f : MetavarContext → MetavarContext) : TacticM Unit := modifyThe Meta.State $ fun s => { s with mctx := f s.mctx }

def saveBacktrackableState : TacticM BacktrackableState := do
env ← getEnv;
mctx ← getMCtx;
s ← get;
pure { env := env, mctx := mctx, goals := s.goals }

def BacktrackableState.restore (b : BacktrackableState) : TacticM Unit := do
setEnv b.env;
setMCtx b.mctx;
modify fun s => { s with goals := b.goals }

@[inline] protected def catch {α} (x : TacticM α) (h : Exception → TacticM α) : TacticM α := do
b ← saveBacktrackableState;
catch x (fun ex => do b.restore; h ex)

@[inline] protected def orelse {α} (x y : TacticM α) : TacticM α := do
catch x (fun _ => y)

instance monadExcept : MonadExcept Exception TacticM :=
{ throw := fun _ => throw,
  catch := fun _ x h => Tactic.catch x h }

instance hasOrElse {α} : HasOrelse (TacticM α) := ⟨Tactic.orelse⟩

structure SavedState :=
(core   : Core.State)
(meta   : Meta.State)
(term   : Term.State)
(tactic : State)

instance SavedState.inhabited : Inhabited SavedState := ⟨⟨arbitrary _, arbitrary _, arbitrary _, arbitrary _⟩⟩

def saveAllState : TacticM SavedState := do
core   ← getThe Core.State;
meta   ← getThe Meta.State;
term   ← getThe Term.State;
tactic ← get;
pure { core := core, meta := meta, term := term, tactic := tactic }

def SavedState.restore (s : SavedState) : TacticM Unit := do
set s.core; set s.meta; set s.term; set s.tactic

private def fromTermException (ex : Term.Exception) : Exception :=
match ex with
| Term.Exception.postpone => unreachable!
| Term.Exception.ex ex    => ex

@[inline] def liftTermElabM {α} (x : TermElabM α) : TacticM α :=
liftM (adaptExcept fromTermException x : Term.ETermElabM Exception α)

@[inline] def liftMetaM {α} (x : MetaM α) : TacticM α :=
liftTermElabM $ Term.liftMetaM x

def instantiateMVars (e : Expr) : TacticM Expr := liftTermElabM $ Term.instantiateMVars e
def addContext (msg : MessageData) : TacticM MessageData := liftTermElabM $ Term.addContext msg
def isExprMVarAssigned (mvarId : MVarId) : TacticM Bool := liftTermElabM $ Term.isExprMVarAssigned mvarId
def assignExprMVar (mvarId : MVarId) (val : Expr) : TacticM Unit := liftTermElabM $ Term.assignExprMVar mvarId val
def ensureHasType (expectedType? : Option Expr) (e : Expr) : TacticM Expr := liftTermElabM $ Term.ensureHasType expectedType? e
def reportUnsolvedGoals (goals : List MVarId) : TacticM Unit := liftTermElabM $ Term.reportUnsolvedGoals goals
def inferType (e : Expr) : TacticM Expr := liftTermElabM $ Term.inferType e
def whnf (e : Expr) : TacticM Expr := liftTermElabM $ Term.whnf e
def whnfCore (e : Expr) : TacticM Expr := liftTermElabM $ Term.whnfCore e
def unfoldDefinition? (e : Expr) : TacticM (Option Expr) := liftTermElabM $ Term.unfoldDefinition? e
def resolveGlobalName (n : Name) : TacticM (List (Name × List String)) := liftTermElabM $ Term.resolveGlobalName n

@[inline] def withRef {α} (ref : Syntax) (x : TacticM α) : TacticM α := do
adaptTheReader Core.Context (Core.Context.replaceRef ref) x

/-- Collect unassigned metavariables -/
def collectMVars (e : Expr) : TacticM (List MVarId) := do
e ← instantiateMVars e;
let s := Lean.collectMVars {} e;
pure s.result.toList

instance monadLog : MonadLog TacticM :=
{ getRef      := liftTermElabM getRef,
  getFileMap  := liftTermElabM getFileMap,
  getFileName := liftTermElabM getFileName,
  addContext  := addContext,
  logMessage  := fun msg => liftTermElabM $ logMessage msg }

def throwErrorAt {α} (ref : Syntax) (msgData : MessageData) : TacticM α := do
liftTermElabM $ Term.throwErrorAt ref msgData

def throwError {α} (msgData : MessageData) : TacticM α := do
liftTermElabM $ Term.throwError msgData

def throwUnsupportedSyntax {α} : TacticM α := liftTermElabM $ Term.throwUnsupportedSyntax

def checkRecDepth : TacticM Unit :=
liftTermElabM $ Term.checkRecDepth

@[inline] def withIncRecDepth {α} (x : TacticM α) : TacticM α := do
checkRecDepth;
adaptTheReader Core.Context Core.Context.incCurrRecDepth x

protected def getCurrMacroScope : TacticM MacroScope := do ctx ← readThe Term.Context; pure ctx.currMacroScope
protected def getMainModule     : TacticM Name       := do env ← getEnv; pure env.mainModule

@[inline] protected def withFreshMacroScope {α} (x : TacticM α) : TacticM α := do
fresh ← modifyGetThe Term.State (fun s => (s.nextMacroScope, { s with nextMacroScope := s.nextMacroScope + 1 }));
adaptTheReader Term.Context (fun ctx => { ctx with currMacroScope := fresh }) x

instance monadQuotation : MonadQuotation TacticM := {
  getCurrMacroScope   := Tactic.getCurrMacroScope,
  getMainModule       := Tactic.getMainModule,
  withFreshMacroScope := @Tactic.withFreshMacroScope
}

unsafe def mkTacticAttribute : IO (KeyedDeclsAttribute Tactic) :=
mkElabAttribute Tactic `Lean.Elab.Tactic.tacticElabAttribute `builtinTactic `tactic `Lean.Parser.Tactic `Lean.Elab.Tactic.Tactic "tactic"
@[init mkTacticAttribute] constant tacticElabAttribute : KeyedDeclsAttribute Tactic := arbitrary _

def logTrace (cls : Name) (msg : MessageData) : TacticM Unit := liftTermElabM $ Term.logTrace cls msg
@[inline] def trace (cls : Name) (msg : Unit → MessageData) : TacticM Unit := liftTermElabM $ Term.trace cls msg
@[inline] def traceAtCmdPos (cls : Name) (msg : Unit → MessageData) : TacticM Unit := liftTermElabM $ Term.traceAtCmdPos cls msg
def dbgTrace {α} [HasToString α] (a : α) : TacticM Unit :=_root_.dbgTrace (toString a) $ fun _ => pure ()

private def evalTacticUsing (s : SavedState) (stx : Syntax) : List Tactic → TacticM Unit
| []                => do
  let refFmt := stx.prettyPrint;
  throwErrorAt stx ("unexpected syntax" ++ MessageData.nest 2 (Format.line ++ refFmt))
| (evalFn::evalFns) => catch (evalFn stx)
  (fun ex => match ex with
    | Exception.io err   => throw ex
    | Exception.error _  =>
      match evalFns with
      | [] => throw ex
      | _  => do s.restore; evalTacticUsing evalFns
    | Exception.unsupportedSyntax => do s.restore; evalTacticUsing evalFns)

/- Elaborate `x` with `stx` on the macro stack -/
@[inline] def withMacroExpansion {α} (beforeStx afterStx : Syntax) (x : TacticM α) : TacticM α :=
adaptTheReader Term.Context (fun ctx => { ctx with macroStack := { before := beforeStx, after := afterStx } :: ctx.macroStack }) x

instance : MonadMacroAdapter TacticM :=
{ getEnv                 := getEnv,
  getCurrMacroScope      := getCurrMacroScope,
  getNextMacroScope      := do s ← getThe Term.State; pure s.nextMacroScope,
  setNextMacroScope      := fun next => modifyThe Term.State $ fun s => { s with nextMacroScope := next },
  getCurrRecDepth        := do ctx ← readThe Core.Context; pure ctx.currRecDepth,
  getMaxRecDepth         := do ctx ← readThe Core.Context; pure ctx.maxRecDepth,
  throwError             := @throwErrorAt,
  throwUnsupportedSyntax := @throwUnsupportedSyntax }

@[specialize] private def expandTacticMacroFns (evalTactic : Syntax → TacticM Unit) (stx : Syntax) : List Macro → TacticM Unit
| []    => throwErrorAt stx ("tactic '" ++ toString stx.getKind ++ "' has not been implemented")
| m::ms => do
  scp  ← getCurrMacroScope;
  catch
    (do stx' ← adaptMacro m stx; evalTactic stx')
    (fun ex => match ms with
      | [] => throw ex
      | _  => expandTacticMacroFns ms)

@[inline] def expandTacticMacro (evalTactic : Syntax → TacticM Unit) (stx : Syntax) : TacticM Unit := do
env ← getEnv;
let k        := stx.getKind;
let table    := (macroAttribute.ext.getState env).table;
let macroFns := (table.find? k).getD [];
expandTacticMacroFns evalTactic stx macroFns

partial def evalTactic : Syntax → TacticM Unit
| stx => withRef stx $ withIncRecDepth $ withFreshMacroScope $ match stx with
  | Syntax.node k args =>
    if k == nullKind then
      -- list of tactics separated by `;` => evaluate in order
      -- Syntax quotations can return multiple ones
      stx.forSepArgsM evalTactic
    else do
      trace `Elab.step fun _ => stx;
      env ← getEnv;
      s ← saveAllState;
      let table := (tacticElabAttribute.ext.getState env).table;
      let k := stx.getKind;
      match table.find? k with
      | some evalFns => evalTacticUsing s stx evalFns
      | none         => expandTacticMacro evalTactic stx
  | _ => throwError "unexpected command"

/-- Adapt a syntax transformation to a regular tactic evaluator. -/
def adaptExpander (exp : Syntax → TacticM Syntax) : Tactic :=
fun stx => do
  stx' ← exp stx;
  withMacroExpansion stx stx' $ evalTactic stx'

@[inline] def withLCtx {α} (lctx : LocalContext) (localInsts : LocalInstances) (x : TacticM α) : TacticM α :=
adaptTheReader Meta.Context (fun ctx => { ctx with lctx := lctx, localInstances := localInsts }) x

def saveAndResetSynthInstanceCache : TacticM Meta.SynthInstanceCache :=
liftTermElabM Term.saveAndResetSynthInstanceCache

def restoreSynthInstanceCache (cache : Meta.SynthInstanceCache) : TacticM Unit :=
liftTermElabM $ Term.restoreSynthInstanceCache cache

/-- Reset `synthInstance` cache, execute `x`, and restore cache -/
@[inline] def resettingSynthInstanceCache {α} (x : TacticM α) : TacticM α := do
savedSythInstance ← saveAndResetSynthInstanceCache;
finally x (restoreSynthInstanceCache savedSythInstance)

@[inline] def resettingSynthInstanceCacheWhen {α} (b : Bool) (x : TacticM α) : TacticM α :=
if b then resettingSynthInstanceCache x else x

def withMVarContext {α} (mvarId : MVarId) (x : TacticM α) : TacticM α := do
mvarDecl   ← getMVarDecl mvarId;
localInsts ← getLocalInsts;
let needReset := localInsts == mvarDecl.localInstances;
withLCtx mvarDecl.lctx mvarDecl.localInstances $ resettingSynthInstanceCacheWhen needReset x

def getGoals : TacticM (List MVarId) := do s ← get; pure s.goals
def setGoals (gs : List MVarId) : TacticM Unit := modify $ fun s => { s with goals := gs }
def appendGoals (gs : List MVarId) : TacticM Unit := modify $ fun s => { s with goals := s.goals ++ gs }
def pruneSolvedGoals : TacticM Unit := do
gs ← getGoals;
gs ← gs.filterM $ fun g => not <$> isExprMVarAssigned g;
setGoals gs
def getUnsolvedGoals : TacticM (List MVarId) := do pruneSolvedGoals; getGoals
def getMainGoal : TacticM (MVarId × List MVarId) := do (g::gs) ← getUnsolvedGoals | throwError "no goals to be solved"; pure (g, gs)
def ensureHasNoMVars (e : Expr) : TacticM Unit := do
e ← instantiateMVars e;
when e.hasMVar $ throwError ("tactic failed, resulting expression contains metavariables" ++ indentExpr e)

def withMainMVarContext {α} (x : TacticM α) : TacticM α := do
(mvarId, _) ← getMainGoal;
withMVarContext mvarId x

@[inline] def liftMetaMAtMain {α} (x : MVarId → MetaM α) : TacticM α := do
(g, _) ← getMainGoal;
withMVarContext g $ liftMetaM $ x g

@[inline] def liftMetaTacticAux {α} (tactic : MVarId → MetaM (α × List MVarId)) : TacticM α := do
(g, gs) ← getMainGoal;
withMVarContext g $ do
  (a, gs') ← liftMetaM $ tactic g;
  setGoals (gs' ++ gs);
  pure a

@[inline] def liftMetaTactic (tactic : MVarId → MetaM (List MVarId)) : TacticM Unit :=
liftMetaTacticAux (fun mvarId => do gs ← tactic mvarId; pure ((), gs))

def done : TacticM Unit := do
gs ← getUnsolvedGoals;
unless gs.isEmpty $ reportUnsolvedGoals gs

def focusAux {α} (tactic : TacticM α) : TacticM α := do
(g, gs) ← getMainGoal;
setGoals [g];
a ← tactic;
gs' ← getGoals;
setGoals (gs' ++ gs);
pure a

def focus {α} (tactic : TacticM α) : TacticM α :=
focusAux (do a ← tactic; done; pure a)

/--
  Use `parentTag` to tag untagged goals at `newGoals`.
  If there are multiple new goals, they are named using `<parentTag>.<newSuffix>_<idx>` where `idx > 0`.
  If there is only one new goal, then we just use `parentTag` -/
def tagUntaggedGoals (parentTag : Name) (newSuffix : Name) (newGoals : List MVarId) : TacticM Unit := do
mctx ← getMCtx;
match newGoals with
| [g] => modifyMCtx $ fun mctx => if mctx.isAnonymousMVar g then mctx.renameMVar g parentTag else mctx
| _   => modifyMCtx $ fun mctx =>
  let (mctx, _) := newGoals.foldl
    (fun (acc : MetavarContext × Nat) (g : MVarId) =>
       let (mctx, idx) := acc;
       if mctx.isAnonymousMVar g then
         (mctx.renameMVar g (parentTag ++ newSuffix.appendIndexAfter idx), idx+1)
       else
         acc)
    (mctx, 1);
  mctx

@[builtinTactic seq] def evalSeq : Tactic :=
fun stx => (stx.getArg 0).forSepArgsM evalTactic

partial def evalChoiceAux (tactics : Array Syntax) : Nat → TacticM Unit
| i =>
  if h : i < tactics.size then
    let tactic := tactics.get ⟨i, h⟩;
    catch
      (evalTactic tactic)
      (fun ex => match ex with
        | Exception.unsupportedSyntax => evalChoiceAux (i+1)
        | _ => throw ex)
  else
    throwUnsupportedSyntax

@[builtinTactic choice] def evalChoice : Tactic :=
fun stx => evalChoiceAux stx.getArgs 0

@[builtinTactic skip] def evalSkip : Tactic :=
fun stx => pure ()

@[builtinTactic failIfSuccess] def evalFailIfSuccess : Tactic :=
fun stx =>
  let tactic := stx.getArg 1;
  whenM
    (catch
      (do evalTactic tactic; pure true)
      (fun _ => pure false))
    (throwError ("tactic succeeded"))

@[builtinTactic traceState] def evalTraceState : Tactic :=
fun stx => do
  gs ← getUnsolvedGoals;
  logInfo (goalsToMessageData gs)

@[builtinTactic «assumption»] def evalAssumption : Tactic :=
fun stx => liftMetaTactic $ fun mvarId => do Meta.assumption mvarId; pure []

@[builtinTactic «intro»] def evalIntro : Tactic :=
fun stx => match_syntax stx with
  | `(tactic| intro)    => liftMetaTactic $ fun mvarId => do (_, mvarId) ← Meta.intro1 mvarId; pure [mvarId]
  | `(tactic| intro $h) => liftMetaTactic $ fun mvarId => do (_, mvarId) ← Meta.intro mvarId h.getId; pure [mvarId]
  | _                   => throwUnsupportedSyntax

private def getIntrosSize : Expr → Nat
| Expr.forallE _ _ b _ => getIntrosSize b + 1
| Expr.letE _ _ _ b _  => getIntrosSize b + 1
| _                    => 0

@[builtinTactic «intros»] def evalIntros : Tactic :=
fun stx => match_syntax stx with
  | `(tactic| intros)       => liftMetaTactic $ fun mvarId => do
    type ← Meta.getMVarType mvarId;
    type ← Meta.instantiateMVars type;
    let n := getIntrosSize type;
    (_, mvarId) ← Meta.introN mvarId n;
    pure [mvarId]
  | `(tactic| intros $ids*) => liftMetaTactic $ fun mvarId => do
    (_, mvarId) ← Meta.introN mvarId ids.size (ids.map Syntax.getId).toList;
    pure [mvarId]
  | _                       => throwUnsupportedSyntax

def getFVarId (id : Syntax) : TacticM FVarId :=
withRef id do
fvar? ← liftTermElabM $ Term.isLocalIdent? id;
match fvar? with
| some fvar => pure fvar.fvarId!
| none      => throwError ("unknown variable '" ++ toString id.getId ++ "'")

def getFVarIds (ids : Array Syntax) : TacticM (Array FVarId) :=
ids.mapM getFVarId

@[builtinTactic «revert»] def evalRevert : Tactic :=
fun stx => match_syntax stx with
  | `(tactic| revert $hs*) => do
     (g, gs) ← getMainGoal;
     withMVarContext g $ do
       fvarIds ← getFVarIds hs;
       (_, g) ← liftMetaM $ Meta.revert g fvarIds;
       setGoals (g :: gs)
  | _                     => throwUnsupportedSyntax

def forEachVar (hs : Array Syntax) (tac : MVarId → FVarId → MetaM MVarId) : TacticM Unit :=
hs.forM $ fun h => do
  (g, gs) ← getMainGoal;
  withMVarContext g $ do
    fvarId ← getFVarId h;
    g ← liftMetaM $ tac g fvarId;
    setGoals (g :: gs)

@[builtinTactic «clear»] def evalClear : Tactic :=
fun stx => match_syntax stx with
  | `(tactic| clear $hs*) => forEachVar hs Meta.clear
  | _                     => throwUnsupportedSyntax

@[builtinTactic «subst»] def evalSubst : Tactic :=
fun stx => match_syntax stx with
  | `(tactic| subst $hs*) => forEachVar hs Meta.subst
  | _                     => throwUnsupportedSyntax

@[builtinTactic paren] def evalParen : Tactic :=
fun stx => evalTactic (stx.getArg 1)

@[builtinTactic nestedTacticBlock] def evalNestedTacticBlock : Tactic :=
fun stx => focus (evalTactic (stx.getArg 1))

@[builtinTactic nestedTacticBlockCurly] def evalNestedTacticBlockCurly : Tactic :=
evalNestedTacticBlock

@[builtinTactic «case»] def evalCase : Tactic :=
fun stx => match_syntax stx with
  | `(tactic| case $tag $tac) => do
     let tag := tag.getId;
     gs ← getUnsolvedGoals;
     some g ← gs.findM? (fun g => do mvarDecl ← getMVarDecl g; pure $ tag.isSuffixOf mvarDecl.userName) | throwError "tag not found";
     let gs := gs.erase g;
     setGoals [g];
     evalTactic tac;
     done;
     setGoals gs
  | _ => throwUnsupportedSyntax

@[builtinTactic «orelse»] def evalOrelse : Tactic :=
fun stx => match_syntax stx with
  | `(tactic| $tac1 <|> $tac2) => evalTactic tac1 <|> evalTactic tac2
  | _                          => throwUnsupportedSyntax

@[init] private def regTraceClasses : IO Unit := do
registerTraceClass `Elab.tactic;
pure ()

end Tactic
end Elab
end Lean
