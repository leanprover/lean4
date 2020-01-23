/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Lean.Util.Sorry
import Init.Lean.Structure
import Init.Lean.Meta
import Init.Lean.Hygiene
import Init.Lean.Util.RecDepth
import Init.Lean.Elab.Log
import Init.Lean.Elab.Alias
import Init.Lean.Elab.ResolveName
import Init.Lean.Elab.Level

namespace Lean
namespace Elab
namespace Term

structure Context extends Meta.Context :=
(fileName        : String)
(fileMap         : FileMap)
(cmdPos          : String.Pos)
(currNamespace   : Name)
(declName?       : Option Name     := none)
(levelNames      : List Name       := [])
(openDecls       : List OpenDecl   := [])
(macroStack      : MacroStack      := [])
(currMacroScope  : MacroScope      := 0)
/- When `mayPostpone == true`, an elaboration function may interrupt its execution by throwing `Exception.postpone`.
   The function `elabTerm` catches this exception and creates fresh synthetic metavariable `?m`, stores `?m` in
   the list of pending synthetic metavariables, and returns `?m`. -/
(mayPostpone     : Bool            := true)
(errToSorry      : Bool            := true)

/-- We use synthetic metavariables as placeholders for pending elaboration steps. -/
inductive SyntheticMVarKind
-- typeclass instance search
| typeClass
-- tactic block execution
| tactic (tacticCode : Syntax)
-- `elabTerm` call that threw `Exception.postpone` (input is stored at `SyntheticMVarDecl.ref`)
| postponed (macroStack : MacroStack)
-- type defaulting (currently: defaulting numeric literals to `Nat`)
| withDefault (defaultVal : Expr)

structure SyntheticMVarDecl :=
(mvarId : MVarId) (ref : Syntax) (kind : SyntheticMVarKind)

structure State extends Meta.State :=
(syntheticMVars  : List SyntheticMVarDecl := [])
(messages        : MessageLog := {})
(instImplicitIdx : Nat := 1)
(anonymousIdx    : Nat := 1)
(nextMacroScope  : Nat := 1)

instance State.inhabited : Inhabited State := ⟨{ env := arbitrary _ }⟩

/-
  The Term elaborator monad has a special kind of exception `Exception.postpone` which is used by
  an elaboration function to notify the main driver that it should be tried later.

  Remark: `Exception.postpone` is used only when `mayPostpone == true` in the `Context`. -/
inductive Exception
| ex       : Elab.Exception → Exception
| postpone : Exception

instance Exception.inhabited : Inhabited Exception := ⟨Exception.postpone⟩
instance Exception.hasToString : HasToString Exception :=
⟨fun ex => match ex with | Exception.postpone => "postponed" | Exception.ex ex => toString ex⟩

/-
  Term elaborator Monad. In principle, we could track statically which methods
  may postpone or not by having adding a Boolean parameter `mayPostpone` to
  `TermElabM`. This would be useful to ensure that `Exception.postpone` does not leak
  to `CommandElabM`, but we abandoned this design because it adds unnecessary complexity. -/
abbrev TermElabM := ReaderT Context (EStateM Exception State)
abbrev TermElab  := Syntax → Option Expr → TermElabM Expr

instance TermElabM.inhabited {α} : Inhabited (TermElabM α) :=
⟨throw $ Exception.postpone⟩

abbrev TermElabResult := EStateM.Result Message State Expr
instance TermElabResult.inhabited : Inhabited TermElabResult := ⟨EStateM.Result.ok (arbitrary _) (arbitrary _)⟩

/--
  Execute `x`, save resulting expression and new state.
  If `x` fails, then it also stores exception and new state.
  Remark: we do not capture `Exception.postpone`. -/
@[inline] def observing (x : TermElabM Expr) : TermElabM TermElabResult :=
fun ctx s =>
  match x ctx s with
  | EStateM.Result.error (Exception.ex (Elab.Exception.error errMsg)) newS => EStateM.Result.ok (EStateM.Result.error errMsg newS) s
  | EStateM.Result.error Exception.postpone _                              => EStateM.Result.error Exception.postpone s
  | EStateM.Result.error ex newS                                           => EStateM.Result.error ex newS
  | EStateM.Result.ok e newS                                               => EStateM.Result.ok (EStateM.Result.ok e newS) s

/--
  Apply the result/exception and state captured with `observing`.
  We use this method to implement overloaded notation and symbols. -/
def applyResult (result : TermElabResult) : TermElabM Expr :=
match result with
| EStateM.Result.ok e s         => do set s; pure e
| EStateM.Result.error errMsg s => do set s; throw (Exception.ex (Elab.Exception.error errMsg))

def getEnv : TermElabM Environment := do s ← get; pure s.env
def getMCtx : TermElabM MetavarContext := do s ← get; pure s.mctx
def getLCtx : TermElabM LocalContext := do ctx ← read; pure ctx.lctx
def getLocalInsts : TermElabM LocalInstances := do ctx ← read; pure ctx.localInstances
def getOptions : TermElabM Options := do ctx ← read; pure ctx.config.opts

def addContext (msg : MessageData) : TermElabM MessageData := do
env ← getEnv; mctx ← getMCtx; lctx ← getLCtx; opts ← getOptions;
pure (MessageData.withContext { env := env, mctx := mctx, lctx := lctx, opts := opts } msg)

instance monadLog : MonadLog TermElabM :=
{ getCmdPos   := do ctx ← read; pure ctx.cmdPos,
  getFileMap  := do ctx ← read; pure ctx.fileMap,
  getFileName := do ctx ← read; pure ctx.fileName,
  addContext  := addContext,
  logMessage  := fun msg => modify $ fun s => { messages := s.messages.add msg, .. s } }

/--
  Throws an error with the given `msgData` and extracting position information from `ref`.
  If `ref` does not contain position information, then use `cmdPos` -/
def throwError {α} (ref : Syntax) (msgData : MessageData) : TermElabM α := do
ctx ← read;
let ref     := getBetterRef ref ctx.macroStack;
let msgData := addMacroStack msgData ctx.macroStack;
msg ← mkMessage msgData MessageSeverity.error ref;
throw (Exception.ex (Elab.Exception.error msg))

def throwUnsupportedSyntax {α} : TermElabM α :=
throw (Exception.ex Elab.Exception.unsupportedSyntax)

@[inline] def withIncRecDepth {α} (ref : Syntax) (x : TermElabM α) : TermElabM α := do
ctx ← read;
when (ctx.currRecDepth == ctx.maxRecDepth) $ throwError ref maxRecDepthErrorMessage;
adaptReader (fun (ctx : Context) => { currRecDepth := ctx.currRecDepth + 1, .. ctx }) x

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

abbrev TermElabTable := ElabFnTable TermElab
def mkBuiltinTermElabTable : IO (IO.Ref TermElabTable) :=  IO.mkRef {}
@[init mkBuiltinTermElabTable] constant builtinTermElabTable : IO.Ref TermElabTable := arbitrary _

def addBuiltinTermElab (k : SyntaxNodeKind) (declName : Name) (elab : TermElab) : IO Unit := do
m ← builtinTermElabTable.get;
when (m.contains k) $
  throw (IO.userError ("invalid builtin term elaborator, elaborator for '" ++ toString k ++ "' has already been defined"));
builtinTermElabTable.modify $ fun m => m.insert k elab

def declareBuiltinTermElab (env : Environment) (kind : SyntaxNodeKind) (declName : Name) : IO Environment :=
let name := `_regBuiltinTermElab ++ declName;
let type := mkApp (mkConst `IO) (mkConst `Unit);
let val  := mkAppN (mkConst `Lean.Elab.Term.addBuiltinTermElab) #[toExpr kind, toExpr declName, mkConst declName];
let decl := Declaration.defnDecl { name := name, lparams := [], type := type, value := val, hints := ReducibilityHints.opaque, isUnsafe := false };
match env.addAndCompile {} decl with
-- TODO: pretty print error
| Except.error _ => throw (IO.userError ("failed to emit registration code for builtin term elaborator '" ++ toString declName ++ "'"))
| Except.ok env  => IO.ofExcept (setInitAttr env name)

@[init] def registerBuiltinTermElabAttr : IO Unit :=
registerBuiltinAttribute {
 name  := `builtinTermElab,
 descr := "Builtin term elaborator",
 add   := fun env declName arg persistent => do {
   unless persistent $ throw (IO.userError ("invalid attribute 'builtinTermElab', must be persistent"));
   kind ← IO.ofExcept $ syntaxNodeKindOfAttrParam env `Lean.Parser.Term arg;
   match env.find? declName with
   | none  => throw $ IO.userError "unknown declaration"
   | some decl =>
     match decl.type with
     | Expr.const `Lean.Elab.Term.TermElab _ _ => declareBuiltinTermElab env kind declName
     | _ => throw (IO.userError ("unexpected term elaborator type at '" ++ toString declName ++ "' `TermElab` expected"))
 },
 applicationTime := AttributeApplicationTime.afterCompilation
}

abbrev TermElabAttribute := ElabAttribute TermElab
def mkTermElabAttribute : IO TermElabAttribute :=
mkElabAttribute TermElab `termElab `Lean.Parser.Term `Lean.Elab.Term.TermElab "term" builtinTermElabTable
@[init mkTermElabAttribute] constant termElabAttribute : TermElabAttribute := arbitrary _

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
def getTraceState : TermElabM TraceState := do s ← get; pure s.traceState
def setTraceState (traceState : TraceState) : TermElabM Unit := modify $ fun s => { traceState := traceState, .. s }
def isExprMVarAssigned (mvarId : MVarId) : TermElabM Bool := do mctx ← getMCtx; pure $ mctx.isExprAssigned mvarId
def getMVarDecl (mvarId : MVarId) : TermElabM MetavarDecl := do mctx ← getMCtx; pure $ mctx.getDecl mvarId
def assignExprMVar (mvarId : MVarId) (val : Expr) : TermElabM Unit := modify $ fun s => { mctx := s.mctx.assignExpr mvarId val, .. s }

def logTrace (cls : Name) (ref : Syntax) (msg : MessageData) : TermElabM Unit := do
ctx ← read;
s   ← get;
logInfo ref $
  MessageData.withContext { env := s.env, mctx := s.mctx, lctx := ctx.lctx, opts := ctx.config.opts } $
    MessageData.tagged cls msg

@[inline] def trace (cls : Name) (ref : Syntax) (msg : Unit → MessageData) : TermElabM Unit := do
opts ← getOptions;
when (checkTraceOption opts cls) $ logTrace cls ref (msg ())

@[inline] def traceAtCmdPos (cls : Name) (msg : Unit → MessageData) : TermElabM Unit :=
trace cls Syntax.missing msg

def dbgTrace {α} [HasToString α] (a : α) : TermElabM Unit :=
_root_.dbgTrace (toString a) $ fun _ => pure ()

/-- Auxiliary function for `liftMetaM` -/
private def mkMessageAux (ctx : Context) (ref : Syntax) (msgData : MessageData) (severity : MessageSeverity) : Message :=
mkMessageCore ctx.fileName ctx.fileMap msgData severity (ref.getPos.getD ctx.cmdPos)

/-- Auxiliary function for `liftMetaM` -/
private def fromMetaException (ctx : Context) (ref : Syntax) (ex : Meta.Exception) : Exception :=
Exception.ex $ Elab.Exception.error $ mkMessageAux ctx ref ex.toMessageData MessageSeverity.error

/-- Auxiliary function for `liftMetaM` -/
private def fromMetaState (ref : Syntax) (ctx : Context) (s : State) (newS : Meta.State) (oldTraceState : TraceState) : State :=
let traces   := newS.traceState.traces;
let messages := traces.foldl (fun (messages : MessageLog) trace => messages.add (mkMessageAux ctx ref trace MessageSeverity.information)) s.messages;
{ toState  := { traceState := oldTraceState, .. newS },
  messages := messages,
  .. s }

@[inline] def liftMetaM {α} (ref : Syntax) (x : MetaM α) : TermElabM α :=
fun ctx s =>
  let oldTraceState := s.traceState;
  match x ctx.toContext { traceState := {}, .. s.toState } with
  | EStateM.Result.ok a newS     => EStateM.Result.ok a (fromMetaState ref ctx s newS oldTraceState)
  | EStateM.Result.error ex newS => EStateM.Result.error (fromMetaException ctx ref ex) (fromMetaState ref ctx s newS oldTraceState)

def ppGoal (ref : Syntax) (mvarId : MVarId) : TermElabM Format := liftMetaM ref $ Meta.ppGoal mvarId
def isDefEq (ref : Syntax) (t s : Expr) : TermElabM Bool := liftMetaM ref $ Meta.approxDefEq $ Meta.isDefEq t s
def inferType (ref : Syntax) (e : Expr) : TermElabM Expr := liftMetaM ref $ Meta.inferType e
def whnf (ref : Syntax) (e : Expr) : TermElabM Expr := liftMetaM ref $ Meta.whnf e
def whnfForall (ref : Syntax) (e : Expr) : TermElabM Expr := liftMetaM ref $ Meta.whnfForall e
def whnfCore (ref : Syntax) (e : Expr) : TermElabM Expr := liftMetaM ref $ Meta.whnfCore e
def unfoldDefinition? (ref : Syntax) (e : Expr) : TermElabM (Option Expr) := liftMetaM ref $ Meta.unfoldDefinition? e
def instantiateMVars (ref : Syntax) (e : Expr) : TermElabM Expr := liftMetaM ref $ Meta.instantiateMVars e
def isClass (ref : Syntax) (t : Expr) : TermElabM (Option Name) := liftMetaM ref $ Meta.isClass t
def mkFreshLevelMVar (ref : Syntax) : TermElabM Level := liftMetaM ref $ Meta.mkFreshLevelMVar
def mkFreshExprMVar (ref : Syntax) (type? : Option Expr := none) (kind : MetavarKind := MetavarKind.natural) (userName? : Name := Name.anonymous) : TermElabM Expr :=
match type? with
| some type => liftMetaM ref $ Meta.mkFreshExprMVar type userName? kind
| none      => liftMetaM ref $ do u ← Meta.mkFreshLevelMVar; type ← Meta.mkFreshExprMVar (mkSort u); Meta.mkFreshExprMVar type userName? kind
def mkFreshTypeMVar (ref : Syntax) (kind : MetavarKind := MetavarKind.natural) (userName? : Name := Name.anonymous) : TermElabM Expr :=
liftMetaM ref $ do u ← Meta.mkFreshLevelMVar; Meta.mkFreshExprMVar (mkSort u) userName? kind
def getLevel (ref : Syntax) (type : Expr) : TermElabM Level := liftMetaM ref $ Meta.getLevel type
def mkForall (ref : Syntax) (xs : Array Expr) (e : Expr) : TermElabM Expr := liftMetaM ref $ Meta.mkForall xs e
def mkForallUsedOnly (ref : Syntax) (xs : Array Expr) (e : Expr) : TermElabM (Expr × Nat) := liftMetaM ref $ Meta.mkForallUsedOnly xs e
def mkLambda (ref : Syntax) (xs : Array Expr) (e : Expr) : TermElabM Expr := liftMetaM ref $ Meta.mkLambda xs e
def mkLet (ref : Syntax) (x : Expr) (e : Expr) : TermElabM Expr := mkLambda ref #[x] e
def trySynthInstance (ref : Syntax) (type : Expr) : TermElabM (LOption Expr) := liftMetaM ref $ Meta.trySynthInstance type
def mkAppM (ref : Syntax) (constName : Name) (args : Array Expr) : TermElabM Expr := liftMetaM ref $ Meta.mkAppM constName args
def decLevel? (ref : Syntax) (u : Level) : TermElabM (Option Level) := liftMetaM ref $ Meta.decLevel? u

def decLevel (ref : Syntax) (u : Level) : TermElabM Level := do
u? ← decLevel? ref u;
match u? with
| some u => pure u
| none   => throwError ref ("invalid universe level, " ++ u ++ " is not greater than 0")

def liftLevelM {α} (x : LevelElabM α) : TermElabM α :=
fun ctx s =>
  match (x { .. ctx }).run { .. s } with
  | EStateM.Result.ok a newS     => EStateM.Result.ok a { mctx := newS.mctx, ngen := newS.ngen, .. s }
  | EStateM.Result.error ex newS => EStateM.Result.error (Exception.ex ex) s

def elabLevel (stx : Syntax) : TermElabM Level :=
liftLevelM $ Level.elabLevel stx

/- Elaborate `x` with `stx` on the macro stack -/
@[inline] def withMacroExpansion {α} (beforeStx afterStx : Syntax) (x : TermElabM α) : TermElabM α :=
adaptReader (fun (ctx : Context) => { macroStack := { before := beforeStx, after := afterStx } :: ctx.macroStack, .. ctx }) x

/-
  Add the given metavariable to the list of pending synthetic metavariables.
  The method `synthesizeSyntheticMVars` is used to process the metavariables on this list. -/
def registerSyntheticMVar (ref : Syntax) (mvarId : MVarId) (kind : SyntheticMVarKind) : TermElabM Unit :=
modify $ fun s => { syntheticMVars := { mvarId := mvarId, ref := ref, kind := kind } :: s.syntheticMVars, .. s }

/-
  Execute `x` without allowing it to postpone elaboration tasks.
  That is, `tryPostpone` is a noop. -/
@[inline] def withoutPostponing {α} (x : TermElabM α) : TermElabM α :=
adaptReader (fun (ctx : Context) => { mayPostpone := false, .. ctx }) x

@[inline] def withNode {α} (stx : Syntax) (x : Syntax → TermElabM α) : TermElabM α :=
match stx with
| Syntax.node _ _ => x stx
| _               => throwError stx ("term elaborator failed, unexpected syntax: " ++ toString stx)

/-- Creates syntax for `(` <ident> `:` <type> `)` -/
def mkExplicitBinder (ident : Syntax) (type : Syntax) : Syntax :=
mkNode `Lean.Parser.Term.explicitBinder #[mkAtom "(", mkNullNode #[ident], mkNullNode #[mkAtom ":", type], mkNullNode, mkAtom ")"]

/-- Convert unassigned universe level metavariables into parameters. -/
def levelMVarToParam (e : Expr) : TermElabM Expr := do
ctx ← read;
mctx ← getMCtx;
let r := mctx.levelMVarToParam (fun n => ctx.levelNames.elem n) e;
modify $ fun s => { mctx := r.mctx, .. s };
pure r.expr

/--
  Auxiliary method for creating fresh binder names.
  Do not confuse with the method for creating fresh free/meta variable ids. -/
def mkFreshAnonymousName : TermElabM Name := do
s ← get;
let anonymousIdx := s.anonymousIdx;
modify $ fun s => { anonymousIdx := s.anonymousIdx + 1, .. s};
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
modify $ fun s => { instImplicitIdx := s.instImplicitIdx + 1, .. s};
pure $ (`_inst).appendIndexAfter instIdx

private partial def isCDot (stx : Syntax) : Bool :=
match_syntax stx with
| `(·) => true
| _    => false

/--
  Auxiliary function for expandind the `·` notation.
  The extra state `Array Syntax` contains the new binder names.
  If `stx` is a `·`, we create a fresh identifier, store in the
  extra state, and return it. Otherwise, we just return `stx`. -/
private def expandCDot (stx : Syntax) : StateT (Array Syntax) TermElabM Syntax :=
withFreshMacroScope $
  match_syntax stx with
  | `(·) => do
     id ← `(a);
     modify $ fun s => s.push id;
     pure id
  | _ => pure stx

/--
  Return `some` if succeeded expanding `·` notation occurring in
  the given syntax. Otherwise, return `none`.
  Examples:
  - `· + 1` => `fun _a_1 => _a_1 + 1`
  - `f · · b` => `fun _a_1 _a_2 => f _a_1 _a_2 b` -/
def expandCDot? (stx : Syntax) : TermElabM (Option Syntax) :=
match_syntax stx with
| `($f $args*) =>
   if args.any isCDot then do
     (args, binders) ← (args.mapM expandCDot).run #[];
     `(fun $binders* => $f $args*)
   else
     pure none
| _ => match stx with
  | Syntax.node k args =>
    if args.any isCDot then do
      (args, binders) ← (args.mapM expandCDot).run #[];
      let newNode := Syntax.node k args;
      `(fun $binders* => $newNode)
    else
      pure none
  | _ => pure none

private def exceptionToSorry (ref : Syntax) (errMsg : Message) (expectedType? : Option Expr) : TermElabM Expr := do
expectedType : Expr ← match expectedType? with
  | none              => mkFreshTypeMVar ref
  | some expectedType => pure expectedType;
u ← getLevel ref expectedType;
-- TODO: should be `(sorryAx.{$u} $expectedType true) when we support antiquotations at that place
let syntheticSorry := mkApp2 (mkConst `sorryAx [u]) expectedType (mkConst `Bool.true);
unless errMsg.data.hasSyntheticSorry $ logMessage errMsg;
pure syntheticSorry

/-- If `mayPostpone == true`, throw `Expection.postpone`. -/
def tryPostpone : TermElabM Unit := do
ctx ← read;
when ctx.mayPostpone $ throw Exception.postpone

/-- If `mayPostpone == true` and `e`'s head is a metavariable, throw `Exception.postpone`. -/
def tryPostponeIfMVar (e : Expr) : TermElabM Unit := do
when e.getAppFn.isMVar $ tryPostpone

def tryPostponeIfNoneOrMVar (e? : Option Expr) : TermElabM Unit :=
match e? with
| some e => tryPostponeIfMVar e
| none   => tryPostpone

private def postponeElabTerm (stx : Syntax) (expectedType? : Option Expr) : TermElabM Expr := do
trace `Elab.postpone stx $ fun _ => stx ++ " : " ++ expectedType?;
mvar ← mkFreshExprMVar stx expectedType? MetavarKind.syntheticOpaque;
ctx ← read;
registerSyntheticMVar stx mvar.mvarId! (SyntheticMVarKind.postponed ctx.macroStack);
pure mvar

/-
  Helper function for `elabTerm` is tries the registered elaboration functions for `stxNode` kind until it finds one that supports the syntax or
  an error is found. -/
private def elabTermUsing (s : State) (stx : Syntax) (expectedType? : Option Expr) (catchExPostpone : Bool)
    : List TermElab → TermElabM Expr
| []                => do
  let refFmt := stx.prettyPrint;
  throwError stx ("unexpected syntax" ++ MessageData.nest 2 (Format.line ++ refFmt))
| (elabFn::elabFns) => catch (elabFn stx expectedType?)
  (fun ex => match ex with
    | Exception.ex (Elab.Exception.error errMsg)    => do ctx ← read; if ctx.errToSorry then exceptionToSorry stx errMsg expectedType? else throw ex
    | Exception.ex Elab.Exception.unsupportedSyntax => do set s; elabTermUsing elabFns
    | Exception.postpone          =>
      if catchExPostpone then do
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
          set s;
          postponeElabTerm stx expectedType?
        else
          throw ex)

instance : MonadMacroAdapter TermElabM :=
{ getEnv                 := getEnv,
  getNameGenerator       := do s ← get; pure s.ngen,
  getCurrMacroScope      := getCurrMacroScope,
  setNameGenerator       := fun ngen => modify $ fun s => { ngen := ngen, .. s },
  throwError             := @throwError,
  throwUnsupportedSyntax := @throwUnsupportedSyntax}

/- Main loop for `elabTerm` -/
partial def elabTermAux (expectedType? : Option Expr) (catchExPostpone := true) : Syntax → TermElabM Expr
| stx => withFreshMacroScope $ withIncRecDepth stx $ withNode stx $ fun node => do
  trace `Elab.step stx $ fun _ => stx;
  s ← get;
  let table := (termElabAttribute.ext.getState s.env).table;
  let k := node.getKind;
  match table.find? k with
  | some elabFns => elabTermUsing s node expectedType? catchExPostpone elabFns
  | none         => do
    env  ← getEnv;
    stx' ← catch
      (adaptMacro (getMacros env) stx)
      (fun ex => match ex with
        | Exception.ex Elab.Exception.unsupportedSyntax => throwError stx ("elaboration function for '" ++ toString k ++ "' has not been implemented")
        | _                                             => throw ex);
    withMacroExpansion stx stx' $ elabTermAux stx'

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
elabTermAux expectedType? catchExPostpone stx

/-- Adapt a syntax transformation to a regular, term-producing elaborator. -/
def adaptExpander (exp : Syntax → TermElabM Syntax) : TermElab :=
fun stx expectedType? => do
  stx' ← exp stx;
  withMacroExpansion stx stx' $ elabTerm stx' expectedType?

/--
  Make sure `e` is a type by inferring its type and making sure it is a `Expr.sort`
  or is unifiable with `Expr.sort`, or can be coerced into one. -/
def ensureType (ref : Syntax) (e : Expr) : TermElabM Expr := do
eType ← inferType ref e;
eType ← whnf ref eType;
if eType.isSort then
  pure e
else do
  u ← mkFreshLevelMVar ref;
  condM (isDefEq ref eType (mkSort u))
    (pure e)
    (do -- TODO try coercion to sort
        throwError ref "type expected")

/-- Elaborate `stx` and ensure result is a type. -/
def elabType (stx : Syntax) : TermElabM Expr := do
u ← mkFreshLevelMVar stx;
type ← elabTerm stx (mkSort u);
ensureType stx type

@[inline] def withLCtx {α} (lctx : LocalContext) (localInsts : LocalInstances) (x : TermElabM α) : TermElabM α :=
adaptReader (fun (ctx : Context) => { lctx := lctx, localInstances := localInsts, .. ctx }) x

def resetSynthInstanceCache : TermElabM Unit :=
modify $ fun s => { cache := { synthInstance := {}, .. s.cache }, .. s }

@[inline] def resettingSynthInstanceCache {α} (x : TermElabM α) : TermElabM α := do
s ← get;
let savedSythInstance := s.cache.synthInstance;
resetSynthInstanceCache;
finally x (modify $ fun s => { cache := { synthInstance := savedSythInstance, .. s.cache }, .. s })

@[inline] def resettingSynthInstanceCacheWhen {α} (b : Bool) (x : TermElabM α) : TermElabM α :=
if b then resettingSynthInstanceCache x else x

/--
  Execute `x` using the given metavariable's `LocalContext` and `LocalInstances`.
  The type class resolution cache is flushed when executing `x` if its `LocalInstances` are
  different from the current ones. -/
def withMVarContext {α} (mvarId : MVarId) (x : TermElabM α) : TermElabM α := do
mvarDecl  ← getMVarDecl mvarId;
ctx       ← read;
let needReset := ctx.localInstances == mvarDecl.localInstances;
withLCtx mvarDecl.lctx mvarDecl.localInstances $ resettingSynthInstanceCacheWhen needReset x

/--
  If `expectedType?` is `some t`, then ensure `t` and `eType` are definitionally equal.
  If they are not, then try coercions.
  Return `some e'` if successful, where `e'` may be different from `e` if coercions have been applied,
  and `none` otherwise
 -/
def tryEnsureHasType? (ref : Syntax) (expectedType? : Option Expr) (eType : Expr) (e : Expr) : TermElabM (Option Expr) :=
match expectedType? with
| none              => pure (some e)
| some expectedType =>
  condM (isDefEq ref eType expectedType)
    (pure (some e))
    -- TODO try `HasCoe`
    (pure none)

/--
  If `expectedType?` is `some t`, then ensure `t` and `eType` are definitionally equal.
  If they are not, then try coercions. -/
def ensureHasTypeAux (ref : Syntax) (expectedType? : Option Expr) (eType : Expr) (e : Expr) : TermElabM Expr := do
e? ← tryEnsureHasType? ref expectedType? eType e;
match e? with
| some e => pure e
| none   =>
  let msg : MessageData :=
    "type mismatch" ++ indentExpr e
    ++ Format.line ++ "has type" ++ indentExpr eType
    ++ Format.line ++ "but it is expected to have type" ++ indentExpr expectedType?.get!;
  throwError ref msg

/--
  If `expectedType?` is `some t`, then ensure `t` and type of `e` are definitionally equal.
  If they are not, then try coercions. -/
def ensureHasType (ref : Syntax) (expectedType? : Option Expr) (e : Expr) : TermElabM Expr :=
match expectedType? with
| none => pure e
| _    => do eType ← inferType ref e; ensureHasTypeAux ref expectedType? eType e

/- Try to synthesize metavariable using type class resolution.
   This method assumes the local context and local instances of `instMVar` coincide
   with the current local context and local instances.
   Return `true` if the instance was synthesized successfully, and `false` if
   the instance contains unassigned metavariables that are blocking the type class
   resolution procedure. Throw an exception if resolution or assignment irrevocably fails. -/
def synthesizeInstMVarCore (ref : Syntax) (instMVar : MVarId) : TermElabM Bool := do
instMVarDecl ← getMVarDecl instMVar;
let type := instMVarDecl.type;
type ← instantiateMVars ref type;
result ← trySynthInstance ref type;
match result with
| LOption.some val => do
  condM (isExprMVarAssigned instMVar)
    (do oldVal ← instantiateMVars ref (mkMVar instMVar);
        unlessM (isDefEq ref oldVal val) $
          throwError ref $
            "synthesized type class instance is not definitionally equal to expression "
            ++ "inferred by typing rules, synthesized" ++ indentExpr val
            ++ Format.line ++ "inferred" ++ indentExpr oldVal)
    (assignExprMVar instMVar val);
  pure true
| LOption.undef    => pure false -- we will try later
| LOption.none     => throwError ref ("failed to synthesize instance" ++ indentExpr type)

def mkInstMVar (ref : Syntax) (type : Expr) : TermElabM Expr := do
mvar ← mkFreshExprMVar ref type MetavarKind.synthetic;
let mvarId := mvar.mvarId!;
unlessM (synthesizeInstMVarCore ref mvarId) $
  registerSyntheticMVar ref mvarId SyntheticMVarKind.typeClass;
pure mvar

/- =======================================
       Builtin elaboration functions
   ======================================= -/

@[builtinTermElab «prop»] def elabProp : TermElab :=
fun _ _ => pure $ mkSort levelZero

@[builtinTermElab «sort»] def elabSort : TermElab :=
fun _ _ => pure $ mkSort levelZero

@[builtinTermElab «type»] def elabTypeStx : TermElab :=
fun _ _ => pure $ mkSort levelOne

@[builtinTermElab «hole»] def elabHole : TermElab :=
fun stx expectedType? => mkFreshExprMVar stx expectedType?

@[builtinTermElab «namedHole»] def elabNamedHole : TermElab :=
fun stx expectedType? =>
  let name := stx.getIdAt 1;
  mkFreshExprMVar stx expectedType? MetavarKind.syntheticOpaque name

def mkTacticMVar (ref : Syntax) (type : Expr) (tacticCode : Syntax) : TermElabM Expr := do
mvar ← mkFreshExprMVar ref type MetavarKind.syntheticOpaque `main;
let mvarId := mvar.mvarId!;
registerSyntheticMVar ref mvarId $ SyntheticMVarKind.tactic tacticCode;
pure mvar

@[builtinTermElab tacticBlock] def elabTacticBlock : TermElab :=
fun stx expectedType? =>
  match expectedType? with
  | some expectedType => mkTacticMVar stx expectedType (stx.getArg 1)
  | none => throwError stx ("invalid tactic block, expected type has not been provided")

/-- Main loop for `mkPairs`. -/
private partial def mkPairsAux (elems : Array Syntax) : Nat → Syntax → TermElabM Syntax
| i, acc =>
  if i > 0 then do
    let i    := i - 1;
    let elem := elems.get! i;
    acc ← `(Prod.mk $elem $acc);
    mkPairsAux i acc
  else
    pure acc

/-- Return syntax `Prod.mk elems[0] (Prod.mk elems[1] ... (Prod.mk elems[elems.size - 2] elems[elems.size - 1])))` -/
def mkPairs (elems : Array Syntax) : TermElabM Syntax :=
mkPairsAux elems (elems.size - 1) elems.back

/--
  Try to expand `·` notation, and if successful elaborate result.
  This method is used to elaborate the Lean parentheses notation.
  Recall that in Lean the `·` notation must be surrounded by parentheses.
  We may change this is the future, but right now, here are valid examples
  - `(· + 1)`
  - `(· + ·)`
  - `(f · a b)` -/
private def elabCDot (stx : Syntax) (expectedType? : Option Expr) : TermElabM Expr := do
stx? ← expandCDot? stx;
match stx? with
| some stx' => withMacroExpansion stx stx' (elabTerm stx' expectedType?)
| none      => elabTerm stx expectedType?

@[builtinTermElab paren] def elabParen : TermElab :=
fun stx expectedType? =>
  let ref := stx;
  match_syntax ref with
  | `(())           => pure $ Lean.mkConst `Unit.unit
  | `(($e : $type)) => do
    type ← elabType type;
    e ← elabCDot e type;
    ensureHasType ref type e
  | `(($e))         => elabCDot e expectedType?
  | `(($e, $es*))   => do
    pairs ← mkPairs (#[e] ++ es.getEvenElems);
    withMacroExpansion stx pairs (elabTerm pairs expectedType?)
  | _ => throwError stx "unexpected parentheses notation"

@[builtinTermElab «listLit»] def elabListLit : TermElab :=
fun stx expectedType? => do
  let openBkt  := stx.getArg 0;
  let args     := stx.getArg 1;
  let closeBkt := stx.getArg 2;
  let consId   := mkTermIdFrom openBkt `List.cons;
  let nilId    := mkTermIdFrom closeBkt `List.nil;
  let newStx   := args.foldSepRevArgs (fun arg r => mkAppStx consId #[arg, r]) nilId;
  elabTerm newStx expectedType?

@[builtinTermElab «arrayLit»] def elabArrayLit : TermElab :=
fun stx expectedType? => do
  match_syntax stx with
  | `(#[$args*]) => do
    newStx ← `(List.toArray [$args*]);
    withMacroExpansion stx newStx (elabTerm newStx expectedType?)
  | _ => throwError stx "unexpected array literal syntax"

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

private def mkFreshLevelMVars (ref : Syntax) (num : Nat) : TermElabM (List Level) :=
num.foldM (fun _ us => do u ← mkFreshLevelMVar ref; pure $ u::us) []

/--
  Create an `Expr.const` using the given name and explicit levels.
  Remark: fresh universe metavariables are created if the constant has more universe
  parameters than `explicitLevels`. -/
def mkConst (ref : Syntax) (constName : Name) (explicitLevels : List Level := []) : TermElabM Expr := do
env ← getEnv;
match env.find? constName with
| none       => throwError ref ("unknown constant '" ++ constName ++ "'")
| some cinfo =>
  if explicitLevels.length > cinfo.lparams.length then
    throwError ref ("too many explicit universe levels")
  else do
    let numMissingLevels := cinfo.lparams.length - explicitLevels.length;
    us ← mkFreshLevelMVars ref numMissingLevels;
    pure $ Lean.mkConst constName (explicitLevels ++ us)

private def mkConsts (ref : Syntax) (candidates : List (Name × List String)) (explicitLevels : List Level) : TermElabM (List (Expr × List String)) := do
env ← getEnv;
candidates.foldlM
  (fun result ⟨constName, projs⟩ => do
    -- TODO: better suppor for `mkConst` failure. We may want to cache the failures, and report them if all candidates fail.
    const ← mkConst ref constName explicitLevels;
    pure $ (const, projs) :: result)
  []

def resolveName (ref : Syntax) (n : Name) (preresolved : List (Name × List String)) (explicitLevels : List Level) : TermElabM (List (Expr × List String)) := do
result? ← resolveLocalName n;
match result? with
| some (e, projs) => do
  unless explicitLevels.isEmpty $
    throwError ref ("invalid use of explicit universe parameters, '" ++ toString e.fvarId! ++ "' is a local");
  pure [(e, projs)]
| none =>
  let process (candidates : List (Name × List String)) : TermElabM (List (Expr × List String)) := do {
    when candidates.isEmpty $
      throwError ref ("unknown identifier '" ++ toString n ++ "'");
    mkConsts ref candidates explicitLevels
  };
  if preresolved.isEmpty then do
    env           ← getEnv;
    currNamespace ← getCurrNamespace;
    openDecls     ← getOpenDecls;
    process (resolveGlobalName env currNamespace openDecls n)
  else
    process preresolved

@[builtinTermElab cdot] def elabBadCDot : TermElab :=
fun stx _ => throwError stx "invalid occurrence of `·` notation, it must be surrounded by parentheses (e.g. `(· + 1)`)"

/-
  A raw literal is not a valid term, but it is nice to have a handler for them because it allows `macros` to insert them into terms.

  TODO: check whether we still need wrapper nodes around literals. -/
@[builtinTermElab strLit] def elabRawStrLit : TermElab :=
fun stx _ => do
  match stx.isStrLit? with
  | some val => pure $ mkStrLit val
  | none     => throwError stx "ill-formed syntax"

@[builtinTermElab str] def elabStr : TermElab :=
fun stx expectedType? => elabRawStrLit (stx.getArg 0) expectedType?

/- See `elabRawStrLit` -/
@[builtinTermElab numLit] def elabRawNumLit : TermElab :=
fun stx expectedType? => do
  let ref := stx;
  val ← match stx.isNatLit? with
    | some val => pure (mkNatLit val)
    | none     => throwError stx "ill-formed syntax";
  typeMVar ← mkFreshTypeMVar ref MetavarKind.synthetic;
  registerSyntheticMVar ref typeMVar.mvarId! (SyntheticMVarKind.withDefault (Lean.mkConst `Nat));
  match expectedType? with
  | some expectedType => do isDefEq ref expectedType typeMVar; pure ()
  | _                 => pure ();
  u ← getLevel ref typeMVar;
  u ← decLevel ref u;
  mvar ← mkInstMVar ref (mkApp (Lean.mkConst `HasOfNat [u]) typeMVar);
  pure $ mkApp3 (Lean.mkConst `HasOfNat.ofNat [u]) typeMVar mvar val

@[builtinTermElab num] def elabNum : TermElab :=
fun stx expectedType? => elabRawNumLit (stx.getArg 0) expectedType?

/- See `elabRawStrLit` -/
@[builtinTermElab charLit] def elabRawCharLit : TermElab :=
fun stx _ => do
  match stx.isCharLit? with
  | some val => pure $ mkApp (Lean.mkConst `Char.ofNat) (mkNatLit val.toNat)
  | none     => throwError stx "ill-formed syntax"

@[builtinTermElab char] def elabChar : TermElab :=
fun stx expectedType? => elabRawCharLit (stx.getArg 0) expectedType?

@[builtinTermElab quotedName] def elabQuotedName : TermElab :=
fun stx _ => match_syntax stx with
| `(`$n) => pure $ toExpr n.getId
| _      => throwUnsupportedSyntax

end Term

@[init] private def regTraceClasses : IO Unit := do
registerTraceClass `Elab.postpone;
pure ()

export Term (TermElabM)

end Elab
end Lean
