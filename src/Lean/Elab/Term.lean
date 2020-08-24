/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Util.Sorry
import Lean.Structure
import Lean.Meta.ExprDefEq
import Lean.Meta.AppBuilder
import Lean.Meta.SynthInstance
import Lean.Meta.Tactic.Util
import Lean.Hygiene
import Lean.Util.RecDepth
import Lean.Elab.Log
import Lean.Elab.Alias
import Lean.Elab.ResolveName
import Lean.Elab.Level

namespace Lean
namespace Elab
namespace Term

structure Context :=
(fileName        : String)
(fileMap         : FileMap)
(currNamespace   : Name)
(declName?       : Option Name     := none)
(levelNames      : List Name       := [])
(openDecls       : List OpenDecl   := [])
(macroStack      : MacroStack      := [])
(currMacroScope  : MacroScope      := firstFrontendMacroScope)
/- When `mayPostpone == true`, an elaboration function may interrupt its execution by throwing `Exception.postpone`.
   The function `elabTerm` catches this exception and creates fresh synthetic metavariable `?m`, stores `?m` in
   the list of pending synthetic metavariables, and returns `?m`. -/
(mayPostpone     : Bool            := true)
/- When `errToSorry` is set to true, the method `elabTerm` catches
   exceptions and converts them into synthetic `sorry`s.
   The implementation of choice nodes and overloaded symbols rely on the fact
   that when `errToSorry` is set to false for an elaboration function `F`, then
   `errToSorry` remains `false` for all elaboration functions invoked by `F`.
   That is, it is safe to transition `errToSorry` from `true` to `false`, but
   we must not set `errToSorry` to `true` when it is currently set to `false`. -/
(errToSorry      : Bool            := true)
/- If `macroStackAtErr == true`, we include it in error messages. -/
(macroStackAtErr : Bool            := true)

/-- We use synthetic metavariables as placeholders for pending elaboration steps. -/
inductive SyntheticMVarKind
-- typeclass instance search
| typeClass
-- Similar to typeClass, but error messages are different,
-- we use "type mismatch" or "application type mismatch" (when `f?` is some) instead of "failed to synthesize"
| coe (expectedType : Expr) (eType : Expr) (e : Expr) (f? : Option Expr)
-- tactic block execution
| tactic (tacticCode : Syntax)
-- `elabTerm` call that threw `Exception.postpone` (input is stored at `SyntheticMVarDecl.ref`)
| postponed (macroStack : MacroStack)
-- type defaulting (currently: defaulting numeric literals to `Nat`)
| withDefault (defaultVal : Expr)

structure SyntheticMVarDecl :=
(mvarId : MVarId) (stx : Syntax) (kind : SyntheticMVarKind)

structure State :=
(syntheticMVars  : List SyntheticMVarDecl := [])
(messages        : MessageLog := {})
(instImplicitIdx : Nat := 1)
(anonymousIdx    : Nat := 1)
(nextMacroScope  : Nat := firstFrontendMacroScope + 1)

instance State.inhabited : Inhabited State := ⟨{}⟩

abbrev TermElabM := ReaderT Context $ StateRefT State $ MetaM
abbrev TermElab  := Syntax → Option Expr → TermElabM Expr

instance TermElabM.inhabited {α} : Inhabited (TermElabM α) :=
⟨throw $ arbitrary _⟩

structure SavedState :=
(core : Core.State)
(meta : Meta.State)
(elab : State)

instance SavedState.inhabited : Inhabited SavedState := ⟨⟨arbitrary _, arbitrary _, arbitrary _⟩⟩

def saveAllState : TermElabM SavedState := do
core ← getThe Core.State;
meta ← getThe Meta.State;
elab ← get;
pure { core := core, meta := meta, elab := elab }

def SavedState.restore (s : SavedState) : TermElabM Unit := do
set s.core; set s.meta; set s.elab

abbrev TermElabResult := EStateM.Result Exception SavedState Expr
instance TermElabResult.inhabited : Inhabited TermElabResult := ⟨EStateM.Result.ok (arbitrary _) (arbitrary _)⟩

/--
  Execute `x`, save resulting expression and new state.
  If `x` fails, then it also stores exception and new state.
  Remark: we do not capture `Exception.postpone`. -/
@[inline] def observing (x : TermElabM Expr) : TermElabM TermElabResult := do
s ← saveAllState;
catch
  (do e ← x; newS ← saveAllState; s.restore; pure (EStateM.Result.ok e newS))
  (fun ex => match ex with
    | Exception.error _ _   => do
      newS ← saveAllState;
      s.restore;
      pure (EStateM.Result.error ex newS)
    | Exception.internal id => do
      when (id == postponeExceptionId) s.restore;
      throw ex)

/--
  Apply the result/exception and state captured with `observing`.
  We use this method to implement overloaded notation and symbols. -/
def applyResult (result : TermElabResult) : TermElabM Expr :=
match result with
| EStateM.Result.ok e s     => do s.restore; pure e
| EStateM.Result.error ex s => do s.restore; throw ex

/-- Auxiliary function for `liftMetaM` -/
private def mkMessageAux (ref : Syntax) (ctx : Context) (msgData : MessageData) (severity : MessageSeverity) : Message :=
let pos := ref.getPos.getD 0;
mkMessageCore ctx.fileName ctx.fileMap msgData severity pos

@[inline] private def liftMetaMCore {α} (x : MetaM α) : TermElabM α := do
liftM $ x

instance : MonadIO TermElabM :=
{ liftIO := fun α x => liftMetaMCore $ liftIO x }

private def saveTraceAsMessages (traceState : TraceState) : TermElabM Unit :=
unless traceState.traces.isEmpty do
  ref ← getRef;
  ctx ← read;
  modify fun s =>
    { s with messages := traceState.traces.foldl
        (fun (messages : MessageLog) trace => messages.add (mkMessageAux ref ctx trace MessageSeverity.information))
        s.messages }

private def liftMetaMFinalizer (oldTraceState : TraceState) : TermElabM Unit := do
newTraceState ← getTraceState;
saveTraceAsMessages newTraceState;
setTraceState oldTraceState

@[inline] def liftMetaM {α} (x : MetaM α) : TermElabM α := do
oldTraceState ← getTraceState;
setTraceState {};
finally (liftMetaMCore x) (liftMetaMFinalizer oldTraceState)

@[inline] def liftCoreM {α} (x : CoreM α) : TermElabM α :=
liftMetaM $ liftM x

def getMCtx : TermElabM MetavarContext := do s ← getThe Meta.State; pure s.mctx
def getLCtx : TermElabM LocalContext := do ctx ← readThe Meta.Context; pure ctx.lctx
def getLocalInsts : TermElabM LocalInstances := do ctx ← readThe Meta.Context; pure ctx.localInstances
def getNGen : TermElabM NameGenerator := do s ← getThe Core.State; pure s.ngen
def getLevelNames : TermElabM (List Name) := do ctx ← read; pure ctx.levelNames
def getFVarLocalDecl! (fvar : Expr) : TermElabM LocalDecl := do
  lctx ← getLCtx;
  match lctx.find? fvar.fvarId! with
  | some d => pure d
  | none   => unreachable!
def getMessageLog : TermElabM MessageLog := do s ← get; pure s.messages

def setMCtx (mctx : MetavarContext) : TermElabM Unit := modifyThe Meta.State $ fun s => { s with mctx := mctx }
def setNGen (ngen : NameGenerator) : TermElabM Unit := modifyThe Core.State $ fun s => { s with ngen := ngen }

private def addContext' (msg : MessageData) : TermElabM MessageData := do
env ← getEnv; mctx ← getMCtx; lctx ← getLCtx; opts ← getOptions;
pure (MessageData.withContext { env := env, mctx := mctx, lctx := lctx, opts := opts } msg)

instance MonadError : MonadError TermElabM :=
{ getRef     := getRef,
  addContext := fun ref msg => do
    ctx ← read;
    let ref := getBetterRef ref ctx.macroStack;
    let msg := if ctx.macroStackAtErr then addMacroStack msg ctx.macroStack else msg;
    msg ← addContext' msg;
    pure (ref, msg) }

instance monadLog : MonadLog TermElabM :=
{ getFileMap  := do ctx ← read; pure ctx.fileMap,
  getFileName := do ctx ← read; pure ctx.fileName,
  addContext  := addContext',
  logMessage  := fun msg => modify $ fun s => { s with messages := s.messages.add msg } }

/- Execute `x` using using `ref` as the default Syntax for providing position information to error messages. -/
@[inline] def withRef {α} (ref : Syntax) (x : TermElabM α) : TermElabM α := do
adaptTheReader Core.Context (Core.Context.replaceRef ref) x

def checkRecDepth : TermElabM Unit :=
liftMetaM $ Meta.checkRecDepth

@[inline] def withIncRecDepth {α} (x : TermElabM α) : TermElabM α := do
checkRecDepth;
adaptTheReader Core.Context Core.Context.incCurrRecDepth x

protected def getCurrMacroScope : TermElabM MacroScope := do ctx ← read; pure ctx.currMacroScope
protected def getMainModule     : TermElabM Name := do env ← getEnv; pure env.mainModule

@[inline] protected def withFreshMacroScope {α} (x : TermElabM α) : TermElabM α := do
fresh ← modifyGet (fun st => (st.nextMacroScope, { st with nextMacroScope := st.nextMacroScope + 1 }));
adaptReader (fun (ctx : Context) => { ctx with currMacroScope := fresh }) x

instance monadQuotation : MonadQuotation TermElabM := {
  getCurrMacroScope   := Term.getCurrMacroScope,
  getMainModule       := Term.getMainModule,
  withFreshMacroScope := @Term.withFreshMacroScope
}

unsafe def mkTermElabAttribute : IO (KeyedDeclsAttribute TermElab) :=
mkElabAttribute TermElab `Lean.Elab.Term.termElabAttribute `builtinTermElab `termElab `Lean.Parser.Term `Lean.Elab.Term.TermElab "term"
@[init mkTermElabAttribute] constant termElabAttribute : KeyedDeclsAttribute TermElab := arbitrary _

/--
  Auxiliary datatatype for presenting a Lean lvalue modifier.
  We represent a unelaborated lvalue as a `Syntax` (or `Expr`) and `List LVal`.
  Example: `a.foo[i].1` is represented as the `Syntax` `a` and the list
  `[LVal.fieldName "foo", LVal.getOp i, LVal.fieldIdx 1]`.
  Recall that the notation `a[i]` is not just for accessing arrays in Lean. -/
inductive LVal
| fieldIdx  (i : Nat)
| fieldName (name : String)
| getOp     (idx : Syntax)

instance LVal.hasToString : HasToString LVal :=
⟨fun p => match p with | LVal.fieldIdx i => toString i | LVal.fieldName n => n | LVal.getOp idx => "[" ++ toString idx ++ "]"⟩

def getDeclName? : TermElabM (Option Name) := do ctx ← read; pure ctx.declName?
def getCurrNamespace : TermElabM Name := do ctx ← read; pure ctx.currNamespace
def getOpenDecls : TermElabM (List OpenDecl) := do ctx ← read; pure ctx.openDecls
def isExprMVarAssigned (mvarId : MVarId) : TermElabM Bool := do mctx ← getMCtx; pure $ mctx.isExprAssigned mvarId
def getMVarDecl (mvarId : MVarId) : TermElabM MetavarDecl := do mctx ← getMCtx; pure $ mctx.getDecl mvarId
def assignExprMVar (mvarId : MVarId) (val : Expr) : TermElabM Unit := modifyThe Meta.State $ fun s => { s with mctx := s.mctx.assignExpr mvarId val }
def assignLevelMVar (mvarId : MVarId) (val : Level) : TermElabM Unit := modifyThe Meta.State $ fun s => { s with mctx := s.mctx.assignLevel mvarId val }

def logTrace (cls : Name) (msg : MessageData) : TermElabM Unit := do
env  ← getEnv;
mctx ← getMCtx;
lctx ← getLCtx;
opts ← getOptions;
logInfo $
  MessageData.withContext { env := env, mctx := mctx, lctx := lctx, opts := opts } $
    MessageData.tagged cls msg

@[inline] def trace (cls : Name) (msg : Unit → MessageData) : TermElabM Unit := do
opts ← getOptions;
when (checkTraceOption opts cls) $ logTrace cls (msg ())

def logDbgTrace (msg : MessageData) : TermElabM Unit := do
trace `Elab.debug $ fun _ => msg

/-- For testing `TermElabM` methods. The #eval command will sign the error. -/
def throwErrorIfErrors : TermElabM Unit := do
s ← get;
when s.messages.hasErrors $
  throwError "Error(s)"

@[inline] def traceAtCmdPos (cls : Name) (msg : Unit → MessageData) : TermElabM Unit :=
withRef Syntax.missing $ trace cls msg

def dbgTrace {α} [HasToString α] (a : α) : TermElabM Unit :=
_root_.dbgTrace (toString a) $ fun _ => pure ()

def ppGoal (mvarId : MVarId) : TermElabM Format := liftMetaM $ Meta.ppGoal mvarId
def isType (e : Expr) : TermElabM Bool := liftMetaM $ Meta.isType e
def isTypeFormer (e : Expr) : TermElabM Bool := liftMetaM $ Meta.isTypeFormer e
def isTypeFormerType (e : Expr) : TermElabM Bool := liftMetaM $ Meta.isTypeFormerType e
def isDefEqNoConstantApprox (t s : Expr) : TermElabM Bool := liftMetaM $ Meta.approxDefEq $ Meta.isDefEq t s
def isDefEq (t s : Expr) : TermElabM Bool := liftMetaM $ Meta.fullApproxDefEq $ Meta.isDefEq t s
def isLevelDefEq (u v : Level) : TermElabM Bool := liftMetaM $ Meta.isLevelDefEq u v
def inferType (e : Expr) : TermElabM Expr := liftMetaM $ Meta.inferType e
def whnf (e : Expr) : TermElabM Expr := liftMetaM $ Meta.whnf e
def whnfForall (e : Expr) : TermElabM Expr := liftMetaM $ Meta.whnfForall e
def whnfCore (e : Expr) : TermElabM Expr := liftMetaM $ Meta.whnfCore e
def unfoldDefinition? (e : Expr) : TermElabM (Option Expr) := liftMetaM $ Meta.unfoldDefinition? e
def instantiateMVars (e : Expr) : TermElabM Expr := liftMetaM $ Meta.instantiateMVars e
def instantiateLevelMVars (u : Level) : TermElabM Level := liftMetaM $ Meta.instantiateLevelMVars u
def isClass? (t : Expr) : TermElabM (Option Name) := liftMetaM $ Meta.isClass? t
def mkFreshId : TermElabM Name := liftMetaM Meta.mkFreshId
def mkFreshLevelMVar : TermElabM Level := liftMetaM $ Meta.mkFreshLevelMVar
def mkFreshExprMVar (type? : Option Expr := none) (kind : MetavarKind := MetavarKind.natural) (userName? : Name := Name.anonymous) : TermElabM Expr :=
match type? with
| some type => liftMetaM $ Meta.mkFreshExprMVar type userName? kind
| none      => liftMetaM $ do u ← Meta.mkFreshLevelMVar; type ← Meta.mkFreshExprMVar (mkSort u); Meta.mkFreshExprMVar type userName? kind
def mkFreshExprMVarWithId (mvarId : MVarId) (type? : Option Expr := none) (kind : MetavarKind := MetavarKind.natural) (userName? : Name := Name.anonymous)
    : TermElabM Expr :=
match type? with
| some type => liftMetaM $ Meta.mkFreshExprMVarWithId mvarId type userName? kind
| none      => liftMetaM $ do u ← Meta.mkFreshLevelMVar; type ← Meta.mkFreshExprMVar (mkSort u); Meta.mkFreshExprMVarWithId mvarId type userName? kind
def mkFreshTypeMVar (kind : MetavarKind := MetavarKind.natural) (userName? : Name := Name.anonymous) : TermElabM Expr :=
liftMetaM $ do u ← Meta.mkFreshLevelMVar; Meta.mkFreshExprMVar (mkSort u) userName? kind
def getLevel (type : Expr) : TermElabM Level := liftMetaM $ Meta.getLevel type
def getLocalDecl (fvarId : FVarId) : TermElabM LocalDecl := liftMetaM $ Meta.getLocalDecl fvarId
def mkForall (xs : Array Expr) (e : Expr) : TermElabM Expr := liftMetaM $ Meta.mkForall xs e
def mkForallUsedOnly (xs : Array Expr) (e : Expr) : TermElabM (Expr × Nat) := liftMetaM $ Meta.mkForallUsedOnly xs e
def mkLambda (xs : Array Expr) (e : Expr) : TermElabM Expr := liftMetaM $ Meta.mkLambda xs e
def mkLet (x : Expr) (e : Expr) : TermElabM Expr := mkLambda #[x] e
def trySynthInstance (type : Expr) : TermElabM (LOption Expr) := liftMetaM $ Meta.trySynthInstance type
def mkAppM (constName : Name) (args : Array Expr) : TermElabM Expr := liftMetaM $ Meta.mkAppM constName args
def mkExpectedTypeHint (e : Expr) (expectedType : Expr) : TermElabM Expr := liftMetaM $ Meta.mkExpectedTypeHint e expectedType
def decLevel? (u : Level) : TermElabM (Option Level) := liftMetaM $ Meta.decLevel? u

def decLevel (u : Level) : TermElabM Level := do
u? ← decLevel? u;
match u? with
| some u => pure u
| none   => throwError ("invalid universe level, " ++ u ++ " is not greater than 0")

/- This function is useful for inferring universe level parameters for function that take arguments such as `{α : Type u}`.
   Recall that `Type u` is `Sort (u+1)` in Lean. Thus, given `α`, we must infer its universe level,
   and then decrement 1 to obtain `u`. -/
def getDecLevel (type : Expr) : TermElabM Level := do
u ← getLevel type;
decLevel u

@[inline] def savingMCtx {α} (x : TermElabM α) : TermElabM α := do
mctx ← getMCtx;
finally x (setMCtx mctx)

def liftLevelM {α} (x : LevelElabM α) : TermElabM α := do
ctx ← read;
ref ← getRef;
mctx ← getMCtx;
ngen ← getNGen;
let lvlCtx : Level.Context := { fileName := ctx.fileName, fileMap := ctx.fileMap, ref := ref, levelNames := ctx.levelNames };
  match (x lvlCtx).run { ngen := ngen, mctx := mctx } with
  | EStateM.Result.ok a newS  => do setMCtx newS.mctx; setNGen newS.ngen; pure a
  | EStateM.Result.error ex _ => throw ex

def elabLevel (stx : Syntax) : TermElabM Level :=
liftLevelM $ Level.elabLevel stx

@[inline] def withConfig {α} (f : Meta.Config → Meta.Config) (x : TermElabM α) : TermElabM α :=
adaptTheReader Meta.Context (fun (ctx : Meta.Context) => { ctx with config := f ctx.config }) x

@[inline] def withTransparency {α} (mode : Meta.TransparencyMode) (x : TermElabM α) : TermElabM α :=
withConfig (fun config => { config with transparency := mode }) x

@[inline] def withReducible {α} (x : TermElabM α) : TermElabM α :=
withTransparency Meta.TransparencyMode.reducible x

/- Elaborate `x` with `stx` on the macro stack -/
@[inline] def withMacroExpansion {α} (beforeStx afterStx : Syntax) (x : TermElabM α) : TermElabM α :=
adaptReader (fun (ctx : Context) => { ctx with macroStack := { before := beforeStx, after := afterStx } :: ctx.macroStack }) x

/-
  Add the given metavariable to the list of pending synthetic metavariables.
  The method `synthesizeSyntheticMVars` is used to process the metavariables on this list. -/
def registerSyntheticMVar (stx : Syntax) (mvarId : MVarId) (kind : SyntheticMVarKind) : TermElabM Unit := do
modify $ fun s => { s with syntheticMVars := { mvarId := mvarId, stx := stx, kind := kind } :: s.syntheticMVars }

def registerSyntheticMVarWithCurrRef (mvarId : MVarId) (kind : SyntheticMVarKind) : TermElabM Unit := do
ref ← getRef;
registerSyntheticMVar ref mvarId kind

/-
  Execute `x` without allowing it to postpone elaboration tasks.
  That is, `tryPostpone` is a noop. -/
@[inline] def withoutPostponing {α} (x : TermElabM α) : TermElabM α :=
adaptReader (fun (ctx : Context) => { ctx with mayPostpone := false }) x

/-- Creates syntax for `(` <ident> `:` <type> `)` -/
def mkExplicitBinder (ident : Syntax) (type : Syntax) : Syntax :=
mkNode `Lean.Parser.Term.explicitBinder #[mkAtom "(", mkNullNode #[ident], mkNullNode #[mkAtom ":", type], mkNullNode, mkAtom ")"]

/--
  Convert unassigned universe level metavariables into parameters.
  The new parameter names are of the form `u_i` where `i >= nextParamIdx`.
  The method returns the updated expression and new `nextParamIdx`.

  Remark: we make sure the generated parameter names do not clash with the universes at `ctx.levelNames`. -/
def levelMVarToParam (e : Expr) (nextParamIdx : Nat := 1) : TermElabM (Expr × Nat) := do
ctx ← read;
mctx ← getMCtx;
let r := mctx.levelMVarToParam (fun n => ctx.levelNames.elem n) e `u nextParamIdx;
setMCtx r.mctx;
pure (r.expr, r.nextParamIdx)

/-- Variant of `levelMVarToParam` where `nextParamIdx` is stored in a state monad. -/
def levelMVarToParam' (e : Expr) : StateT Nat TermElabM Expr := do
nextParamIdx ← get;
(e, nextParamIdx) ← liftM $ levelMVarToParam e nextParamIdx;
set nextParamIdx;
pure e

/--
  Auxiliary method for creating fresh binder names.
  Do not confuse with the method for creating fresh free/meta variable ids. -/
def mkFreshAnonymousName : TermElabM Name := do
s ← get;
let anonymousIdx := s.anonymousIdx;
modify $ fun s => { s with anonymousIdx := s.anonymousIdx + 1 };
pure $ (`_a).appendIndexAfter anonymousIdx

/--
  Auxiliary method for creating a `Syntax.ident` containing
  a fresh name. This method is intended for creating fresh binder names.
  It is just a thin layer on top of `mkFreshAnonymousName`. -/
def mkFreshAnonymousIdent (ref : Syntax) : TermElabM Syntax := do
n ← mkFreshAnonymousName;
pure $ mkIdentFrom ref n

/--
  Auxiliary method for creating binder names for local instances.
  Users expect them to be named as `_inst_<idx>`. -/
def mkFreshInstanceName : TermElabM Name := do
s ← get;
let instIdx := s.instImplicitIdx;
modify $ fun s => { s with instImplicitIdx := s.instImplicitIdx + 1 };
pure $ (`_inst).appendIndexAfter instIdx

private partial def hasCDot : Syntax → Bool
| Syntax.node k args =>
  if k == `Lean.Parser.Term.paren then false
  else if k == `Lean.Parser.Term.cdot then true
  else args.any hasCDot
| _ => false

/--
  Auxiliary function for expandind the `·` notation.
  The extra state `Array Syntax` contains the new binder names.
  If `stx` is a `·`, we create a fresh identifier, store in the
  extra state, and return it. Otherwise, we just return `stx`. -/
private partial def expandCDot : Syntax → StateT (Array Syntax) MacroM Syntax
| stx@(Syntax.node k args) =>
  if k == `Lean.Parser.Term.paren then pure stx
  else if k == `Lean.Parser.Term.cdot then withFreshMacroScope $ do
    id ← `(a);
    modify $ fun s => s.push id;
    pure id
  else do
    args ← args.mapM expandCDot;
    pure $ Syntax.node k args
| stx => pure stx

/--
  Return `some` if succeeded expanding `·` notation occurring in
  the given syntax. Otherwise, return `none`.
  Examples:
  - `· + 1` => `fun _a_1 => _a_1 + 1`
  - `f · · b` => `fun _a_1 _a_2 => f _a_1 _a_2 b` -/
def expandCDot? (stx : Syntax) : MacroM (Option Syntax) :=
if hasCDot stx then do
  (newStx, binders) ← (expandCDot stx).run #[];
  `(fun $binders* => $newStx)
else
  pure none

def mkFreshFVarId : TermElabM FVarId :=
liftMetaM $ Meta.mkFreshId

def withLocalDecl {α} (n : Name) (binderInfo : BinderInfo) (type : Expr) (k : Expr → TermElabM α) : TermElabM α := do
fvarId     ← mkFreshFVarId;
lctx       ← getLCtx;
localInsts ← getLocalInsts;
let lctx   := lctx.mkLocalDecl fvarId n type binderInfo;
let fvar   := mkFVar fvarId;
c?         ← isClass? type;
match c? with
| some c => adaptTheReader Meta.Context
    (fun ctx => { ctx with lctx := lctx, localInstances := localInsts.push { className := c, fvar := fvar } }) $
    k fvar
| none   => adaptTheReader Meta.Context (fun ctx => { ctx with lctx := lctx }) $ k fvar

def withLetDecl {α} (n : Name) (type : Expr) (val : Expr) (k : Expr → TermElabM α) : TermElabM α := do
fvarId     ← mkFreshFVarId;
lctx       ← getLCtx;
localInsts ← getLocalInsts;
let lctx   := lctx.mkLetDecl fvarId n type val;
let fvar   := mkFVar fvarId;
c?         ← isClass? type;
match c? with
| some c => adaptTheReader Meta.Context
              (fun ctx => { ctx with lctx := lctx, localInstances := localInsts.push { className := c, fvar := fvar } }) $
              k fvar
| none   => adaptTheReader Meta.Context (fun ctx => { ctx with lctx := lctx }) $ k fvar

def throwTypeMismatchError {α} (expectedType : Expr) (eType : Expr) (e : Expr)
    (f? : Option Expr := none) (extraMsg? : Option MessageData := none) : TermElabM α :=
let extraMsg : MessageData := match extraMsg? with
  | none          => Format.nil
  | some extraMsg => Format.line ++ extraMsg;
match f? with
| none =>
  let msg : MessageData :=
    "type mismatch" ++ indentExpr e
    ++ Format.line ++ "has type" ++ indentExpr eType
    ++ Format.line ++ "but it is expected to have type" ++ indentExpr expectedType
    ++ extraMsg;
  throwError msg
| some f => liftMetaM $ Meta.throwAppTypeMismatch f e extraMsg

@[inline] def withoutMacroStackAtErr {α} (x : TermElabM α) : TermElabM α :=
adaptReader (fun (ctx : Context) => { ctx with macroStackAtErr := false }) x

/- Try to synthesize metavariable using type class resolution.
   This method assumes the local context and local instances of `instMVar` coincide
   with the current local context and local instances.
   Return `true` if the instance was synthesized successfully, and `false` if
   the instance contains unassigned metavariables that are blocking the type class
   resolution procedure. Throw an exception if resolution or assignment irrevocably fails. -/
def synthesizeInstMVarCore (instMVar : MVarId) : TermElabM Bool := do
instMVarDecl ← getMVarDecl instMVar;
let type := instMVarDecl.type;
type ← instantiateMVars type;
result ← trySynthInstance type;
match result with
| LOption.some val => do
  condM (isExprMVarAssigned instMVar)
    (do oldVal ← instantiateMVars (mkMVar instMVar);
        unlessM (isDefEq oldVal val) $
          throwError $
            "synthesized type class instance is not definitionally equal to expression "
            ++ "inferred by typing rules, synthesized" ++ indentExpr val
            ++ Format.line ++ "inferred" ++ indentExpr oldVal)
    (assignExprMVar instMVar val);
  pure true
| LOption.undef    => pure false -- we will try later
| LOption.none     => throwError ("failed to synthesize instance" ++ indentExpr type)

/--
  Try to apply coercion to make sure `e` has type `expectedType`.
  Relevant definitions:
  ```
  class CoeT (α : Sort u) (a : α) (β : Sort v)
  abbrev coe {α : Sort u} {β : Sort v} (a : α) [CoeT α a β] : β
  ``` -/
def tryCoe (expectedType : Expr) (eType : Expr) (e : Expr) (f? : Option Expr) : TermElabM Expr :=
condM (isDefEq expectedType eType) (pure e) $ do
u ← getLevel eType;
v ← getLevel expectedType;
let coeTInstType := mkAppN (mkConst `CoeT [u, v]) #[eType, e, expectedType];
mvar ← mkFreshExprMVar coeTInstType MetavarKind.synthetic;
let eNew := mkAppN (mkConst `coe [u, v]) #[eType, expectedType, e, mvar];
let mvarId := mvar.mvarId!;
catch
  (withoutMacroStackAtErr $ do
    unlessM (synthesizeInstMVarCore mvarId) $
      registerSyntheticMVarWithCurrRef mvarId (SyntheticMVarKind.coe expectedType eType e f?);
    pure eNew)
  (fun ex =>
    match ex with
    | Exception.error _ msg => throwTypeMismatchError expectedType eType e f? msg
    | _                     => throwTypeMismatchError expectedType eType e f?)

private def isTypeApp? (type : Expr) : TermElabM (Option (Expr × Expr)) := do
type ← withReducible $ whnf type;
match type with
| Expr.app m α _ => pure (some (m, α))
| _              => pure none

structure IsMonadResult :=
(m    : Expr)
(α    : Expr)
(inst : Expr)

private def isMonad? (type : Expr) : TermElabM (Option IsMonadResult) := do
type ← withReducible $ whnf type;
match type with
| Expr.app m α _ =>
  catch
    (do
      monadType ← mkAppM `Monad #[m];
      result    ← trySynthInstance monadType;
      match result with
      | LOption.some inst => pure (some { m := m, α := α, inst := inst })
      | _                 => pure none)
    (fun _ => pure none)
| _              => pure none

def synthesizeInst (type : Expr) : TermElabM Expr := do
type ← instantiateMVars type;
result ← trySynthInstance type;
match result with
| LOption.some val => pure val
| LOption.undef    => throwError ("failed to synthesize instance" ++ indentExpr type)
| LOption.none     => throwError ("failed to synthesize instance" ++ indentExpr type)

/--
  Try to coerce `a : α` into `m β` by first coercing `a : α` into ‵β`, and then using `pure`.
  The method is only applied if the head of `α` nor ‵β` is not a metavariable. -/
private def tryPureCoe? (m β α a : Expr) : TermElabM (Option Expr) :=
if β.getAppFn.isMVar || α.getAppFn.isMVar then pure none
else catch
 (do
   aNew ← tryCoe β α a none;
   aNew ← liftMetaM $ Meta.mkPure m aNew;
   pure $ some aNew)
 (fun _ => pure none)

/-
Try coercions and monad lifts to make sure `e` has type `expectedType`.

If `expectedType` is of the form `n β` where `n` is a Monad, we try monad lifts and other extensions.
Otherwise, we just use the basic `tryCoe`.

Extensions for monads.

Given an expected type of the form `n β`, if `eType` is of the form `α`

1 - Try to coerce ‵α` into ‵β`, and use `pure` to lift it to `n α`.

If `eType` is of the form `m α`. We use the following approaches.

1- Try to unify `n` and `m`. If it succeeds, then we rely on `tryCoe`, and
   the instances
   ```
   instance coeMethod {m : Type u → Type v} {α β : Type u} [∀ a, CoeT α a β] [Monad m] : Coe (m α) (m β)
   instance pureCoeDepProp {m : Type → Type v} [HasPure m] {p : Prop} [Decidable p] : CoeDep (m Prop) (pure p) (m Bool)
   ```

2- If there is monad lift from `m` to `n` and we can unify `α` and `β`, we use
  ```
  liftM : ∀ {m : Type u_1 → Type u_2} {n : Type u_1 → Type u_3} [self : HasMonadLiftT m n] {α : Type u_1}, m α → n α
  ```

3- If there is a monad lif from `m` to `n` and a coercion from `α` to `β`, we use
  ```
  liftCoeM {m : Type u → Type v} {n : Type u → Type w} {α β : Type u} [HasMonadLiftT m n] [∀ a, CoeT α a β] [Monad n] (x : m α) : n β
  ```

Note that approach 3 does not subsume 1 because it is only applicable if there is a coercion from `α` to `β` for all values in `α`.
This is not the case for example for `pure $ x > 0` when the expected type is `IO Bool`. The given type is `IO Prop`, and
we only have a coercion from decidable propositions.  Approach 1 works because it constructs the coercion `CoeT (m Prop) (pure $ x > 0) (m Bool)`
using the instance `pureCoeDepProp`.

Note that, approach 2 is more powerful than `tryCoe`.
Recall that type class resolution never assigns metavariables created by other modules.
Now, consider the following scenario
```lean
def g (x : Nat) : IO Nat := ...
deg h (x : Nat) : StateT Nat IO Nat := do
v ← g x;
IO.Println v;
...
```
Let's assume there is no other occurrence of `v` in `h`.
Thus, we have that the expected of `g x` is `StateT Nat IO ?α`,
and the given type is `IO Nat`. So, even if we add a coercion.
```
instance {α m n} [HasLiftT m n] {α} : Coe (m α) (n α) := ...
```
It is not applicable because TC would have to assign `?α := Nat`.
On the other hand, TC can easily solve `[HasLiftT IO (StateT Nat IO)]`
since this goal does not contain any metavariables. And then, we
convert `g x` into `liftM $ g x`.
-/
def tryLiftAndCoe (expectedType : Expr) (eType : Expr) (e : Expr) (f? : Option Expr) : TermElabM Expr := do
eType ← instantiateMVars eType;
some ⟨n, β, monadInst⟩ ← isMonad? expectedType | tryCoe expectedType eType e f?;
β ← instantiateMVars β;
eNew? ← tryPureCoe? n β eType e;
match eNew? with
| some eNew => pure eNew
| none      => do
some (m, α) ← isTypeApp? eType | tryCoe expectedType eType e f?;
condM (isDefEq m n) (tryCoe expectedType eType e f?) $
  catch
    (do
      -- Construct lift from `m` to `n`
      hasMonadLiftType ← mkAppM `HasMonadLiftT #[m, n];
      hasMonadLiftVal  ← synthesizeInst hasMonadLiftType;
      u_1 ← getDecLevel α;
      u_2 ← getDecLevel eType;
      u_3 ← getDecLevel expectedType;
      let eNew := mkAppN (Lean.mkConst `liftM [u_1, u_2, u_3]) #[m, n, hasMonadLiftVal, α, e];
      eNewType ← inferType eNew;
      condM (isDefEq expectedType eNewType)
        (pure eNew) -- approach 2 worked
        (do
          u ← getLevel α;
          v ← getLevel β;
          let coeTInstType := Lean.mkForall `a BinderInfo.default α $ mkAppN (mkConst `CoeT [u, v]) #[α, mkBVar 0, β];
          coeTInstVal ← synthesizeInst coeTInstType;
          let eNew := mkAppN (Lean.mkConst `liftCoeM [u_1, u_2, u_3]) #[m, n, α, β, hasMonadLiftVal, coeTInstVal, monadInst, e];
          eNewType ← inferType eNew;
          condM (isDefEq expectedType eNewType)
            (pure eNew) -- approach 3 worked
            (throwTypeMismatchError expectedType eType e f?)))
    (fun _ => throwTypeMismatchError expectedType eType e f?)

/--
  If `expectedType?` is `some t`, then ensure `t` and `eType` are definitionally equal.
  If they are not, then try coercions.

  Argument `f?` is used only for generating error messages. -/
def ensureHasTypeAux (expectedType? : Option Expr) (eType : Expr) (e : Expr) (f? : Option Expr := none) : TermElabM Expr :=
match expectedType? with
| none              => pure e
| some expectedType =>
  /-
    Recall that constant approximation is used to solve constraint of the form
    ```
    ?m t =?= s
    ```
    where `t` is an arbitrary term, by assigning `?m := fun _ => s`
    This approximation when not used carefully produces bad solutions, and may prevent coercions from being tried.
    For example, consider the term `pure (x > 0)` with inferred type `?m Prop` and expected type `IO Bool`. In this situation, the
    elaborator generates the unification constraint
    ```
    ?m Prop =?= IO Bool
    ```
    It is not a higher-order pattern, not first-order approximation is applicable. However, constant approximation
    produces the bogus solution `?m := fun _ => IO Bool`, and prevents the system from using the coercion from
    the decidable proposition `x > 0` to `Bool`.

    On the other hand, the constant approximation is desirable for elaborating the term
    ```
    let f (x : _) := pure 0; f ()
    ```
    with expected type `StateT Nat Id Nat`.
    In this example, the following unification contraint is generated.
    ```
    ?m () (?n ()) =?= StateT Nat Id Nat
    ```
    It is not a higher-order pattern, and first-order approximation fails.
    However, constant approximation solves it by assigning
    ```
    ?m := fun _ => StateT Nat Id
    ?n := fun _ => Nat
    ```
    Note that `f`s type is `(x : ?α) -> ?m x (?n x)`. The metavariables `?m` and `?n` may depend on `x`.

    The `isDefEqNoConstantApprox` fails to unify the expected and inferred types. Then, `tryLiftAndCoe` first tries
    the monadic extensions, and then falls back to `isDefEq` which enables all approximations.
  -/
  condM (isDefEqNoConstantApprox eType expectedType)
    (pure e)
    (tryLiftAndCoe expectedType eType e f?)

/--
  If `expectedType?` is `some t`, then ensure `t` and type of `e` are definitionally equal.
  If they are not, then try coercions. -/
def ensureHasType (expectedType? : Option Expr) (e : Expr) : TermElabM Expr :=
match expectedType? with
| none => pure e
| _    => do eType ← inferType e; ensureHasTypeAux expectedType? eType e

def logException (ex : Exception) : TermElabM Unit := do
match ex with
| Exception.error ref msg => withRef ref $ logError msg
| Exception.internal id   => do
  name ← liftIO $ id.getName;
  logError ("internal exception: " ++ name)

private def exceptionToSorry (ex : Exception) (expectedType? : Option Expr) : TermElabM Expr := do
expectedType : Expr ← match expectedType? with
  | none              => mkFreshTypeMVar
  | some expectedType => pure expectedType;
u ← getLevel expectedType;
-- TODO: should be `(sorryAx.{$u} $expectedType true) when we support antiquotations at that place
let syntheticSorry := mkApp2 (mkConst `sorryAx [u]) expectedType (mkConst `Bool.true);
unless ex.hasSyntheticSorry $ logException ex;
pure syntheticSorry

/-- If `mayPostpone == true`, throw `Expection.postpone`. -/
def tryPostpone : TermElabM Unit := do
ctx ← read;
when ctx.mayPostpone $ throwPostpone

/-- If `mayPostpone == true` and `e`'s head is a metavariable, throw `Exception.postpone`. -/
def tryPostponeIfMVar (e : Expr) : TermElabM Unit := do
when e.getAppFn.isMVar do
  e ← instantiateMVars e;
  when e.getAppFn.isMVar $ tryPostpone

def tryPostponeIfNoneOrMVar (e? : Option Expr) : TermElabM Unit :=
match e? with
| some e => tryPostponeIfMVar e
| none   => tryPostpone

private def postponeElabTerm (stx : Syntax) (expectedType? : Option Expr) : TermElabM Expr := do
trace `Elab.postpone $ fun _ => stx ++ " : " ++ expectedType?;
mvar ← mkFreshExprMVar expectedType? MetavarKind.syntheticOpaque;
ctx ← read;
registerSyntheticMVar stx mvar.mvarId! (SyntheticMVarKind.postponed ctx.macroStack);
pure mvar

/-
  Helper function for `elabTerm` is tries the registered elaboration functions for `stxNode` kind until it finds one that supports the syntax or
  an error is found. -/
private def elabUsingElabFnsAux (s : SavedState) (stx : Syntax) (expectedType? : Option Expr) (catchExPostpone : Bool)
    : List TermElab → TermElabM Expr
| []                => do
  let refFmt := stx.prettyPrint;
  throwError ("unexpected syntax" ++ MessageData.nest 2 (Format.line ++ refFmt))
| (elabFn::elabFns) => catch (elabFn stx expectedType?)
  (fun ex => match ex with
    | Exception.error _ _ => do
      ctx ← read;
      if ctx.errToSorry then
        exceptionToSorry ex expectedType?
      else
        throw ex
    | Exception.internal id =>
      if id == unsupportedSyntaxExceptionId then do
        s.restore;
        elabUsingElabFnsAux elabFns
      else if catchExPostpone && id == postponeExceptionId then do
        /- If `elab` threw `Exception.postpone`, we reset any state modifications.
           For example, we want to make sure pending synthetic metavariables created by `elab` before
           it threw `Exception.postpone` are discarded.
           Note that we are also discarding the messages created by `elab`.

           For example, consider the expression.
           `((f.x a1).x a2).x a3`
           Now, suppose the elaboration of `f.x a1` produces an `Exception.postpone`.
           Then, a new metavariable `?m` is created. Then, `?m.x a2` also throws `Exception.postpone`
           because the type of `?m` is not yet known. Then another, metavariable `?n` is created, and
          finally `?n.x a3` also throws `Exception.postpone`. If we did not restore the state, we would
          keep "dead" metavariables `?m` and `?n` on the pending synthetic metavariable list. This is
          wasteful because when we resume the elaboration of `((f.x a1).x a2).x a3`, we start it from scratch
          and new metavariables are created for the nested functions. -/
          s.restore;
          postponeElabTerm stx expectedType?
        else
          throw ex)

def elabUsingElabFns (stx : Syntax) (expectedType? : Option Expr) (catchExPostpone : Bool) : TermElabM Expr := do
s ← saveAllState;
env ← getEnv;
let table := (termElabAttribute.ext.getState env).table;
let k := stx.getKind;
match table.find? k with
| some elabFns => elabUsingElabFnsAux s stx expectedType? catchExPostpone elabFns
| none         => throwError ("elaboration function for '" ++ toString k ++ "' has not been implemented")

instance : MonadMacroAdapter TermElabM :=
{ getEnv                 := getEnv,
  getCurrMacroScope      := getCurrMacroScope,
  getNextMacroScope      := do s ← get; pure s.nextMacroScope,
  setNextMacroScope      := fun next => modify $ fun s => { s with nextMacroScope := next },
  getCurrRecDepth        := do ctx ← readThe Core.Context; pure ctx.currRecDepth,
  getMaxRecDepth         := do ctx ← readThe Core.Context; pure ctx.maxRecDepth,
  throwError             := fun α ref msg => throwErrorAt ref msg,
  throwUnsupportedSyntax := fun α => throwUnsupportedSyntax}

private def isExplicit (stx : Syntax) : Bool :=
match_syntax stx with
| `(@$f) => true
| _      => false

private def isExplicitApp (stx : Syntax) : Bool :=
stx.getKind == `Lean.Parser.Term.app && isExplicit (stx.getArg 0)

/--
  Return true if `stx` if a lambda abstraction containing a `{}` or `[]` binder annotation.
  Example: `fun {α} (a : α) => a` -/
private def isLambdaWithImplicit (stx : Syntax) : Bool :=
match_syntax stx with
| `(fun $binders* => $body) => binders.any $ fun b => b.isOfKind `Lean.Parser.Term.implicitBinder || b.isOfKind `Lean.Parser.Term.instBinder
| _                         => false

partial def dropTermParens : Syntax → Syntax | stx =>
match_syntax stx with
| `(($stx)) => dropTermParens stx
| _         => stx

/-- Block usage of implicit lambdas if `stx` is `@f` or `@f arg1 ...` or `fun` with an implicit binder annotation. -/
def blockImplicitLambda (stx : Syntax) : Bool :=
let stx := dropTermParens stx;
isExplicit stx || isExplicitApp stx || isLambdaWithImplicit stx

/--
  Return normalized expected type if it is of the form `{a : α} → β` or `[a : α] → β` and
  `blockImplicitLambda stx` is not true, else return `none`. -/
def useImplicitLambda? (stx : Syntax) (expectedType? : Option Expr) : TermElabM (Option Expr) :=
if blockImplicitLambda stx then pure none
else match expectedType? with
  | some expectedType => do
    expectedType ← whnfForall expectedType;
    match expectedType with
    | Expr.forallE _ _ _ c => pure $ if c.binderInfo.isExplicit then none else some expectedType
    | _                    => pure $ none
  | _         => pure $ none

def elabImplicitLambdaAux (stx : Syntax) (catchExPostpone : Bool) (expectedType : Expr) (fvars : Array Expr) : TermElabM Expr := do
body ← elabUsingElabFns stx expectedType catchExPostpone;
-- body ← ensureHasType stx expectedType body;
r ← mkLambda fvars body;
trace `Elab.implicitForall $ fun _ => r;
pure r

partial def elabImplicitLambda (stx : Syntax) (catchExPostpone : Bool) : Expr → Array Expr → TermElabM Expr
| type@(Expr.forallE n d b c), fvars =>
  if c.binderInfo.isExplicit then
    elabImplicitLambdaAux stx catchExPostpone type fvars
  else withFreshMacroScope $ do
    n ← MonadQuotation.addMacroScope n;
    withLocalDecl n c.binderInfo d $ fun fvar => do
      type ← whnfForall (b.instantiate1 fvar);
      elabImplicitLambda type (fvars.push fvar)
| type, fvars =>
  elabImplicitLambdaAux stx catchExPostpone type fvars

/- Main loop for `elabTerm` -/
partial def elabTermAux (expectedType? : Option Expr) (catchExPostpone : Bool) (implicitLambda : Bool) : Syntax → TermElabM Expr
| stx => withFreshMacroScope $ withIncRecDepth do
  trace `Elab.step $ fun _ => expectedType? ++ " " ++ stx;
  env ← getEnv;
  stxNew? ← catchInternalId unsupportedSyntaxExceptionId
    (do newStx ← adaptMacro (getMacros env) stx; pure (some newStx))
    (fun _ => pure none);
  match stxNew? with
  | some stxNew => withMacroExpansion stx stxNew $ elabTermAux stxNew
  | _ => do
    implicit? ← if implicitLambda then useImplicitLambda? stx expectedType? else pure none;
    match implicit? with
    | some expectedType => elabImplicitLambda stx catchExPostpone expectedType #[]
    | none              => elabUsingElabFns stx expectedType? catchExPostpone

/--
  Main function for elaborating terms.
  It extracts the elaboration methods from the environment using the node kind.
  Recall that the environment has a mapping from `SyntaxNodeKind` to `TermElab` methods.
  It creates a fresh macro scope for executing the elaboration method.
  All unlogged trace messages produced by the elaboration method are logged using
  the position information at `stx`. If the elaboration method throws an `Exception.error` and `errToSorry == true`,
  the error is logged and a synthetic sorry expression is returned.
  If the elaboration throws `Exception.postpone` and `catchExPostpone == true`,
  a new synthetic metavariable of kind `SyntheticMVarKind.postponed` is created, registered,
  and returned.
  The option `catchExPostpone == false` is used to implement `resumeElabTerm`
  to prevent the creation of another synthetic metavariable when resuming the elaboration. -/
def elabTerm (stx : Syntax) (expectedType? : Option Expr) (catchExPostpone := true) : TermElabM Expr :=
withRef stx $ elabTermAux expectedType? catchExPostpone true stx

def elabTermEnsuringType (stx : Syntax) (expectedType? : Option Expr) : TermElabM Expr := do
e ← elabTerm stx expectedType?;
withRef stx $ ensureHasType expectedType? e

def elabTermWithoutImplicitLambdas (stx : Syntax) (expectedType? : Option Expr) (catchExPostpone := true) : TermElabM Expr := do
elabTermAux expectedType? catchExPostpone false stx

/-- Adapt a syntax transformation to a regular, term-producing elaborator. -/
def adaptExpander (exp : Syntax → TermElabM Syntax) : TermElab :=
fun stx expectedType? => do
  stx' ← exp stx;
  withMacroExpansion stx stx' $ elabTerm stx' expectedType?

@[inline] def withLCtx {α} (lctx : LocalContext) (localInsts : LocalInstances) (x : TermElabM α) : TermElabM α :=
adaptTheReader Meta.Context (fun ctx => { ctx with lctx := lctx, localInstances := localInsts }) x

def saveAndResetSynthInstanceCache : TermElabM Meta.SynthInstanceCache :=
liftMetaMCore Meta.saveAndResetSynthInstanceCache

def resetSynthInstanceCache : TermElabM Unit := do
_ ← saveAndResetSynthInstanceCache; pure ()

def restoreSynthInstanceCache (cache : Meta.SynthInstanceCache) : TermElabM Unit :=
liftMetaMCore $ Meta.restoreSynthInstanceCache cache

/-- Reset `synthInstance` cache, execute `x`, and restore cache -/
@[inline] def resettingSynthInstanceCache {α} (x : TermElabM α) : TermElabM α := do
savedSythInstance ← saveAndResetSynthInstanceCache;
finally x (restoreSynthInstanceCache savedSythInstance)

@[inline] def resettingSynthInstanceCacheWhen {α} (b : Bool) (x : TermElabM α) : TermElabM α :=
if b then resettingSynthInstanceCache x else x

def withLocalContext {α} (lctx : LocalContext) (localInsts : LocalInstances) (x : TermElabM α) : TermElabM α := do
localInstsCurr ← getLocalInsts;
adaptTheReader Meta.Context (fun ctx => { ctx with lctx := lctx, localInstances := localInsts }) $
  if localInsts == localInstsCurr then
    x
  else
    resettingSynthInstanceCache x

/--
  Execute `x` using the given metavariable's `LocalContext` and `LocalInstances`.
  The type class resolution cache is flushed when executing `x` if its `LocalInstances` are
  different from the current ones. -/
def withMVarContext {α} (mvarId : MVarId) (x : TermElabM α) : TermElabM α := do
mvarDecl   ← getMVarDecl mvarId;
localInsts ← getLocalInsts;
let needReset := localInsts == mvarDecl.localInstances;
withLCtx mvarDecl.lctx mvarDecl.localInstances $ resettingSynthInstanceCacheWhen needReset x

def mkInstMVar (type : Expr) : TermElabM Expr := do
mvar ← mkFreshExprMVar type MetavarKind.synthetic;
let mvarId := mvar.mvarId!;
unlessM (synthesizeInstMVarCore mvarId) $
  registerSyntheticMVarWithCurrRef mvarId SyntheticMVarKind.typeClass;
pure mvar

/-
  Relevant definitions:
  ```
  class CoeSort (α : Sort u) (β : outParam (Sort v))
  abbrev coeSort {α : Sort u} {β : Sort v} (a : α) [CoeSort α β] : β
  ``` -/
private def tryCoeSort (α : Expr) (a : Expr) : TermElabM Expr := do
β ← mkFreshTypeMVar;
u ← getLevel α;
v ← getLevel β;
let coeSortInstType := mkAppN (Lean.mkConst `CoeSort [u, v]) #[α, β];
mvar ← mkFreshExprMVar coeSortInstType MetavarKind.synthetic;
let mvarId := mvar.mvarId!;
catch
  (withoutMacroStackAtErr $ condM (synthesizeInstMVarCore mvarId)
    (pure $ mkAppN (Lean.mkConst `coeSort [u, v]) #[α, β, a, mvar])
    (throwError "type expected"))
  (fun ex =>
    match ex with
    | Exception.error _ msg => throwError $ "type expected" ++ Format.line ++ msg
    | _                     => throwError "type expected")

/--
  Make sure `e` is a type by inferring its type and making sure it is a `Expr.sort`
  or is unifiable with `Expr.sort`, or can be coerced into one. -/
def ensureType (e : Expr) : TermElabM Expr :=
condM (isType e)
  (pure e)
  (do
    eType ← inferType e;
    u ← mkFreshLevelMVar;
    condM (isDefEq eType (mkSort u))
      (pure e)
      (tryCoeSort eType e))

/-- Elaborate `stx` and ensure result is a type. -/
def elabType (stx : Syntax) : TermElabM Expr := do
u ← mkFreshLevelMVar;
type ← elabTerm stx (mkSort u);
withRef stx $ ensureType type

def addDecl (decl : Declaration) : TermElabM Unit := do
env ← getEnv;
match env.addDecl decl with
| Except.ok    env => setEnv env
| Except.error kex => do opts ← getOptions; throwError (kex.toMessageData opts)

def compileDecl (decl : Declaration) : TermElabM Unit := do
env  ← getEnv;
opts ← getOptions;
match env.compileDecl opts decl with
| Except.ok env    => setEnv env
| Except.error kex => throwError (kex.toMessageData opts)

def mkAuxDefinition (declName : Name) (type : Expr) (value : Expr) (zeta : Bool := false) : TermElabM Expr := do
env ← getEnv;
opts ← getOptions;
mctx ← getMCtx;
lctx ← getLCtx;
match Lean.mkAuxDefinition env opts mctx lctx declName type value zeta with
| Except.error ex          => throwError (ex.toMessageData opts)
| Except.ok (r, env, mctx) => do
  setEnv env;
  setMCtx mctx;
  pure r

private partial def mkAuxNameAux (env : Environment) (base : Name) : Nat → Name
| i =>
  let candidate := base.appendIndexAfter i;
  if env.contains candidate then
    mkAuxNameAux (i+1)
  else
    candidate

def mkAuxName (suffix : Name) : TermElabM Name := do
env ← getEnv;
ctx ← read;
match ctx.declName? with
| none          => throwError "auxiliary declaration cannot be created when declaration name is not available"
| some declName => pure $ mkAuxNameAux env (declName ++ suffix) 1

/- =======================================
       Builtin elaboration functions
   ======================================= -/

@[builtinTermElab «prop»] def elabProp : TermElab :=
fun _ _ => pure $ mkSort levelZero

private def elabOptLevel (stx : Syntax) : TermElabM Level :=
if stx.isNone then
  pure levelZero
else
  elabLevel $ stx.getArg 0

@[builtinTermElab «sort»] def elabSort : TermElab :=
fun stx _ => do
  u ← elabOptLevel $ stx.getArg 1;
  pure $ mkSort u

@[builtinTermElab «type»] def elabTypeStx : TermElab :=
fun stx _ => do
  u ← elabOptLevel $ stx.getArg 1;
  pure $ mkSort (mkLevelSucc u)

@[builtinTermElab «hole»] def elabHole : TermElab :=
fun stx expectedType? => mkFreshExprMVar expectedType?

@[builtinTermElab «namedHole»] def elabNamedHole : TermElab :=
fun stx expectedType? =>
  let name := stx.getIdAt 1;
  mkFreshExprMVar expectedType? MetavarKind.syntheticOpaque name

def mkTacticMVar (type : Expr) (tacticCode : Syntax) : TermElabM Expr := do
mvar ← mkFreshExprMVar type MetavarKind.syntheticOpaque `main;
let mvarId := mvar.mvarId!;
registerSyntheticMVar tacticCode mvarId $ SyntheticMVarKind.tactic tacticCode;
pure mvar

@[builtinTermElab tacticBlock] def elabTacticBlock : TermElab :=
fun stx expectedType? =>
  match expectedType? with
  | some expectedType => mkTacticMVar expectedType (stx.getArg 1)
  | none => throwError ("invalid tactic block, expected type has not been provided")

@[builtinTermElab byTactic] def elabByTactic : TermElab :=
fun stx expectedType? =>
  match expectedType? with
  | some expectedType => mkTacticMVar expectedType (stx.getArg 1)
  | none => throwError ("invalid 'by' tactic, expected type has not been provided")

/-- Main loop for `mkPairs`. -/
private partial def mkPairsAux (elems : Array Syntax) : Nat → Syntax → MacroM Syntax
| i, acc =>
  if i > 0 then do
    let i    := i - 1;
    let elem := elems.get! i;
    acc ← `(Prod.mk $elem $acc);
    mkPairsAux i acc
  else
    pure acc

/-- Return syntax `Prod.mk elems[0] (Prod.mk elems[1] ... (Prod.mk elems[elems.size - 2] elems[elems.size - 1])))` -/
def mkPairs (elems : Array Syntax) : MacroM Syntax :=
mkPairsAux elems (elems.size - 1) elems.back

/--
  Try to expand `·` notation, and if successful elaborate result.
  This method is used to elaborate the Lean parentheses notation.
  Recall that in Lean the `·` notation must be surrounded by parentheses.
  We may change this is the future, but right now, here are valid examples
  - `(· + 1)`
  - `(f ⟨·, 1⟩ ·)`
  - `(· + ·)`
  - `(f · a b)` -/
private def elabCDot (stx : Syntax) (expectedType? : Option Expr) : TermElabM Expr := do
stx? ← liftMacroM $ expandCDot? stx;
match stx? with
| some stx' => withMacroExpansion stx stx' (elabTerm stx' expectedType?)
| none      => elabTerm stx expectedType?

@[builtinTermElab paren] def elabParen : TermElab :=
fun stx expectedType? =>
  match_syntax stx with
  | `(())           => pure $ Lean.mkConst `Unit.unit
  | `(($e : $type)) => do
    type ← elabType type;
    e ← elabCDot e type;
    ensureHasType type e
  | `(($e))         => elabCDot e expectedType?
  | `(($e, $es*))   => do
    pairs ← liftMacroM $ mkPairs (#[e] ++ es.getEvenElems);
    withMacroExpansion stx pairs (elabTerm pairs expectedType?)
  | _ => throwError "unexpected parentheses notation"

@[builtinMacro Lean.Parser.Term.listLit] def expandListLit : Macro :=
fun stx =>
  let openBkt  := stx.getArg 0;
  let args     := stx.getArg 1;
  let closeBkt := stx.getArg 2;
  let consId   := mkIdentFrom openBkt `List.cons;
  let nilId    := mkIdentFrom closeBkt `List.nil;
  pure $ args.foldSepRevArgs (fun arg r => mkAppStx consId #[arg, r]) nilId

@[builtinMacro Lean.Parser.Term.arrayLit] def expandArrayLit : Macro :=
fun stx =>
  match_syntax stx with
  | `(#[$args*]) => `(List.toArray [$args*])
  | _            => throw $ Macro.Exception.error stx "unexpected array literal syntax"

private partial def resolveLocalNameAux (lctx : LocalContext) : Name → List String → Option (Expr × List String)
| n, projs =>
  match lctx.findFromUserName? n with
  | some decl => some (decl.toExpr, projs)
  | none      => match n with
    | Name.str pre s _ => resolveLocalNameAux pre (s::projs)
    | _                => none

private def resolveLocalName (n : Name) : TermElabM (Option (Expr × List String)) := do
lctx ← getLCtx;
pure $ resolveLocalNameAux lctx n []

/- Return true iff `stx` is a `Syntax.ident`, and it is a local variable. -/
def isLocalIdent? (stx : Syntax) : TermElabM (Option Expr) :=
match stx with
| Syntax.ident _ _ val _ => do
  r? ← resolveLocalName val;
  match r? with
  | some (fvar, []) => pure (some fvar)
  | _               => pure none
| _ => pure none

private def mkFreshLevelMVars (num : Nat) : TermElabM (List Level) :=
num.foldM (fun _ us => do u ← mkFreshLevelMVar; pure $ u::us) []

/--
  Create an `Expr.const` using the given name and explicit levels.
  Remark: fresh universe metavariables are created if the constant has more universe
  parameters than `explicitLevels`. -/
def mkConst (constName : Name) (explicitLevels : List Level := []) : TermElabM Expr := do
env ← getEnv;
match env.find? constName with
| none       => throwError ("unknown constant '" ++ constName ++ "'")
| some cinfo =>
  if explicitLevels.length > cinfo.lparams.length then
    throwError ("too many explicit universe levels")
  else do
    let numMissingLevels := cinfo.lparams.length - explicitLevels.length;
    us ← mkFreshLevelMVars numMissingLevels;
    pure $ Lean.mkConst constName (explicitLevels ++ us)

private def mkConsts (candidates : List (Name × List String)) (explicitLevels : List Level) : TermElabM (List (Expr × List String)) := do
env ← getEnv;
candidates.foldlM
  (fun result ⟨constName, projs⟩ => do
    -- TODO: better suppor for `mkConst` failure. We may want to cache the failures, and report them if all candidates fail.
    const ← mkConst constName explicitLevels;
    pure $ (const, projs) :: result)
  []

def resolveGlobalName (n : Name) : TermElabM (List (Name × List String)) := do
env ← getEnv;
currNamespace ← getCurrNamespace;
openDecls ← getOpenDecls;
pure (Lean.Elab.resolveGlobalName env currNamespace openDecls n)

def resolveName (n : Name) (preresolved : List (Name × List String)) (explicitLevels : List Level) : TermElabM (List (Expr × List String)) := do
result? ← resolveLocalName n;
match result? with
| some (e, projs) => do
  unless explicitLevels.isEmpty $
    throwError ("invalid use of explicit universe parameters, '" ++ e ++ "' is a local");
  pure [(e, projs)]
| none =>
  let process (candidates : List (Name × List String)) : TermElabM (List (Expr × List String)) := do {
    when candidates.isEmpty $ do {
      mainModule ← getMainModule;
      let view := extractMacroScopes n;
      throwError ("unknown identifier '" ++ view.format mainModule ++ "'")
    };
    mkConsts candidates explicitLevels
  };
  if preresolved.isEmpty then do
    r ← resolveGlobalName n;
    process r
  else
    process preresolved

@[builtinTermElab cdot] def elabBadCDot : TermElab :=
fun stx _ => throwError "invalid occurrence of `·` notation, it must be surrounded by parentheses (e.g. `(· + 1)`)"

@[builtinTermElab strLit] def elabStrLit : TermElab :=
fun stx _ => do
  match stx.isStrLit? with
  | some val => pure $ mkStrLit val
  | none     => throwError "ill-formed syntax"

@[builtinTermElab numLit] def elabNumLit : TermElab :=
fun stx expectedType? => do
  val ← match stx.isNatLit? with
    | some val => pure (mkNatLit val)
    | none     => throwError "ill-formed syntax";
  typeMVar ← mkFreshTypeMVar MetavarKind.synthetic;
  registerSyntheticMVar stx typeMVar.mvarId! (SyntheticMVarKind.withDefault (Lean.mkConst `Nat));
  match expectedType? with
  | some expectedType => do _ ← isDefEq expectedType typeMVar; pure ()
  | _                 => pure ();
  u ← getLevel typeMVar;
  u ← decLevel u;
  mvar ← mkInstMVar (mkApp (Lean.mkConst `HasOfNat [u]) typeMVar);
  pure $ mkApp3 (Lean.mkConst `HasOfNat.ofNat [u]) typeMVar mvar val

@[builtinTermElab charLit] def elabCharLit : TermElab :=
fun stx _ => do
  match stx.isCharLit? with
  | some val => pure $ mkApp (Lean.mkConst `Char.ofNat) (mkNatLit val.toNat)
  | none     => throwError "ill-formed syntax"

@[builtinTermElab quotedName] def elabQuotedName : TermElab :=
fun stx _ =>
  match (stx.getArg 0).isNameLit? with
  | some val => pure $ toExpr val
  | none     => throwError "ill-formed syntax"

private def mkSomeContext : Context :=
{ fileName      := "<TermElabM>",
  fileMap       := arbitrary _,
  currNamespace := Name.anonymous }

@[inline] def TermElabM.run {α} (x : TermElabM α) (ctx : Context := mkSomeContext) (s : State := {}) : MetaM (α × State) :=
(x.run ctx).run s

@[inline] def TermElabM.run' {α} (x : TermElabM α) (ctx : Context := mkSomeContext) (s : State := {}) : MetaM α :=
Prod.fst <$> x.run ctx s

@[inline] def TermElabM.toIO {α} (x : TermElabM α)
    (ctxCore : Core.Context) (sCore : Core.State)
    (ctxMeta : Meta.Context) (sMeta : Meta.State)
    (ctx : Context) (s : State) : IO (α × Core.State × Meta.State × State) := do
((a, s), sCore, sMeta) ← (x.run ctx s).toIO ctxCore sCore ctxMeta sMeta;
pure (a, sCore, sMeta, s)

instance MetaHasEval {α} [MetaHasEval α] : MetaHasEval (TermElabM α) :=
⟨fun env opts x _ => MetaHasEval.eval env opts $ x.run' mkSomeContext⟩

end Term

@[init] private def regTraceClasses : IO Unit := do
registerTraceClass `Elab.postpone;
registerTraceClass `Elab.coe;
registerTraceClass `Elab.debug;
pure ()

export Term (TermElabM)

end Elab
end Lean
