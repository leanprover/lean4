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
import Init.Lean.Elab.Log
import Init.Lean.Elab.Alias
import Init.Lean.Elab.ResolveName

namespace Lean
namespace Elab
namespace Term

structure Context extends Meta.Context :=
(fileName        : String)
(fileMap         : FileMap)
(cmdPos          : String.Pos)
(currNamespace   : Name)
(univNames       : List Name       := [])
(openDecls       : List OpenDecl   := [])
(macroStack      : List Syntax     := [])
(currMacroScope  : MacroScope := 0)
/- When `mayPostpone == true`, an elaboration function may interrupt its execution by throwing `Exception.postpone`.
   The function `elabTerm` catches this exception and creates fresh synthetic metavariable `?m`, stores `?m` in
   the list of pending synthetic metavariables, and returns `?m`. -/
(mayPostpone     : Bool            := true)

inductive SyntheticMVarKind
| typeClass
| tactic (tacticCode : Syntax)
| postponed (macroStack : List Syntax)
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
| error    : Elab.Exception → Exception
| postpone : Exception

instance Exception.inhabited : Inhabited Exception := ⟨Exception.postpone⟩
instance Exception.hasToString : HasToString Exception :=
⟨fun ex => match ex with | Exception.postpone => "posponed" | Exception.error ex => toString ex⟩

/-
  Term elaborator Monad. In principle, we could track statically which methods
  may postpone or not by having adding a Boolean parameter `mayPostpone` to
  `TermElabM`. This would be useful to ensure that `Exception.postpone` does not leak
  to `CommandElabM`, but we abandoned this design because it adds unnecessary complexity. -/
abbrev TermElabM := ReaderT Context (EStateM Exception State)
abbrev TermElab  := SyntaxNode → Option Expr → TermElabM Expr

instance TermElabM.inhabited {α} : Inhabited (TermElabM α) :=
⟨throw $ Exception.postpone⟩

abbrev TermElabResult := EStateM.Result Elab.Exception State Expr
instance TermElabResult.inhabited : Inhabited TermElabResult := ⟨EStateM.Result.ok (arbitrary _) (arbitrary _)⟩

/--
  Execute `x`, save resulting expression and new state.
  If `x` fails, then it also stores exception and new state.
  Remark: we do not capture `Exception.postpone`. -/
@[inline] def observing (x : TermElabM Expr) : TermElabM TermElabResult :=
fun ctx s =>
  match x ctx s with
  | EStateM.Result.error Exception.postpone newS   => EStateM.Result.error Exception.postpone newS
  | EStateM.Result.error (Exception.error ex) newS => EStateM.Result.ok (EStateM.Result.error ex newS) s
  | EStateM.Result.ok e newS                       => EStateM.Result.ok (EStateM.Result.ok e newS) s

/--
  Apply the result/exception and state captured with `observing`.
  We use this method to implement overloaded notation and symbols. -/
def applyResult (result : TermElabResult) : TermElabM Expr :=
match result with
| EStateM.Result.ok e s     => do set s; pure e
| EStateM.Result.error ex s => do set s; throw (Exception.error ex)

instance TermElabM.monadLog : MonadLog TermElabM :=
{ getCmdPos   := do ctx ← read; pure ctx.cmdPos,
  getFileMap  := do ctx ← read; pure ctx.fileMap,
  getFileName := do ctx ← read; pure ctx.fileName,
  logMessage  := fun msg => modify $ fun s => { messages := s.messages.add msg, .. s } }

/--
  Throws an error with the given `msgData` and extracting position information from `ref`.
  If `ref` does not contain position information, then use `cmdPos` -/
def throwError {α} (ref : Syntax) (msgData : MessageData) : TermElabM α := do
msg ← mkMessage msgData MessageSeverity.error ref;
throw (Exception.error msg)

protected def getCurrMacroScope : TermElabM Nat := do
ctx ← read;
pure ctx.currMacroScope

@[inline] protected def withFreshMacroScope {α} (x : TermElabM α) : TermElabM α := do
fresh ← modifyGet (fun st => (st.nextMacroScope, { st with nextMacroScope := st.nextMacroScope + 1 }));
adaptReader (fun (ctx : Context) => { ctx with currMacroScope := fresh }) x

instance TermElabM.MonadQuotation : MonadQuotation TermElabM := {
  getCurrMacroScope   := Term.getCurrMacroScope,
  withFreshMacroScope := @Term.withFreshMacroScope
}

abbrev TermElabTable := SMap SyntaxNodeKind TermElab
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
registerAttribute {
 name  := `builtinTermElab,
 descr := "Builtin term elaborator",
 add   := fun env declName arg persistent => do {
   unless persistent $ throw (IO.userError ("invalid attribute 'builtinTermElab', must be persistent"));
   kind ← syntaxNodeKindOfAttrParam env `Lean.Parser.Term arg;
   match env.find? declName with
   | none  => throw "unknown declaration"
   | some decl =>
     match decl.type with
     | Expr.const `Lean.Elab.Term.TermElab _ _ => declareBuiltinTermElab env kind declName
     | _ => throw (IO.userError ("unexpected term elaborator type at '" ++ toString declName ++ "' `TermElab` expected"))
 },
 applicationTime := AttributeApplicationTime.afterCompilation
}

abbrev TermElabAttribute := ElabAttribute TermElabTable
def mkTermElabAttribute : IO TermElabAttribute := mkElabAttribute `elabTerm "term" builtinTermElabTable
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

def getEnv : TermElabM Environment := do s ← get; pure s.env
def getMCtx : TermElabM MetavarContext := do s ← get; pure s.mctx
def getCurrNamespace : TermElabM Name := do ctx ← read; pure ctx.currNamespace
def getOpenDecls : TermElabM (List OpenDecl) := do ctx ← read; pure ctx.openDecls
def getLCtx : TermElabM LocalContext := do ctx ← read; pure ctx.lctx
def getLocalInsts : TermElabM LocalInstances := do ctx ← read; pure ctx.localInstances
def getOptions : TermElabM Options := do ctx ← read; pure ctx.config.opts
def getTraceState : TermElabM TraceState := do s ← get; pure s.traceState
def setTraceState (traceState : TraceState) : TermElabM Unit := modify $ fun s => { traceState := traceState, .. s }
def isExprMVarAssigned (mvarId : MVarId) : TermElabM Bool := do mctx ← getMCtx; pure $ mctx.isExprAssigned mvarId
def getMVarDecl (mvarId : MVarId) : TermElabM MetavarDecl := do mctx ← getMCtx; pure $ mctx.getDecl mvarId
def assignExprMVar (mvarId : MVarId) (val : Expr) : TermElabM Unit := modify $ fun s => { mctx := s.mctx.assignExpr mvarId val, .. s }

/--
  Wraps the given message with the current contextual information: environment, metavariable context, and local context.
  We need the context to be able to invoke the pretty printer. -/
def addContext (msg : MessageData) : TermElabM MessageData := do
ctx ← read;
s   ← get;
pure $ MessageData.context s.env s.mctx ctx.lctx msg

instance tracer : SimpleMonadTracerAdapter TermElabM :=
{ getOptions       := getOptions,
  getTraceState    := getTraceState,
  addContext       := addContext,
  modifyTraceState := fun f => modify $ fun s => { traceState := f s.traceState, .. s } }

def dbgTrace {α} [HasToString α] (a : α) : TermElabM Unit :=
_root_.dbgTrace (toString a) $ fun _ => pure ()

/-- Auxiliary function for `liftMetaM` -/
private def mkMessageAux (ctx : Context) (ref : Syntax) (msgData : MessageData) (severity : MessageSeverity) : Message :=
mkMessageCore ctx.fileName ctx.fileMap msgData severity (ref.getPos.getD ctx.cmdPos)

/-- Auxiliary function for `liftMetaM` -/
private def fromMetaException (ctx : Context) (ref : Syntax) (ex : Meta.Exception) : Exception :=
Exception.error $ mkMessageAux ctx ref ex.toMessageData MessageSeverity.error

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

def isDefEq (ref : Syntax) (t s : Expr) : TermElabM Bool := liftMetaM ref $ Meta.isDefEq t s
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

/- Elaborate `x` with `stx` on the macro stack -/
@[inline] def withMacroExpansion {α} (stx : Syntax) (x : TermElabM α) : TermElabM α :=
adaptReader (fun (ctx : Context) => { macroStack := stx :: ctx.macroStack, .. ctx }) x

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

@[inline] def withNode {α} (stx : Syntax) (x : SyntaxNode → TermElabM α) : TermElabM α :=
stx.ifNode x (fun _ => throwError stx ("term elaborator failed, unexpected syntax: " ++ toString stx))

/-- Execute `x` and logs all unlogged trace messages produced by `x` using position `pos`. -/
@[inline] def tracingAtPos {α} (pos : String.Pos) (x : TermElabM α) : TermElabM α := do
oldTraceState ← getTraceState;
setTraceState {};
finally x $ do
  traceState ← getTraceState;
  traceState.traces.forM $ logInfoAt pos;
  setTraceState oldTraceState

/-- Similar to `tracingAt`, but uses `ref` to obtain position information. -/
@[inline] def tracingAt {α} (ref : Syntax) (x : TermElabM α) : TermElabM α := do
ctx ← read;
tracingAtPos (ref.getPos.getD ctx.cmdPos) x

/-- Creates syntax for `(` <ident> `:` <type> `)` -/
def mkExplicitBinder (ident : Syntax) (type : Syntax) : Syntax :=
mkNode `Lean.Parser.Term.explicitBinder #[mkAtom "(", mkNullNode #[ident], mkNullNode #[mkAtom ":", type], mkNullNode, mkAtom ")"]

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

def mkHole := mkNode `Lean.Parser.Term.hole #[mkAtom "_"]

/-- Convert a `Syntax.ident` into a `Lean.Parser.Term.id` node -/
def mkTermIdFromIdent (ident : Syntax) : Syntax :=
match ident with
| Syntax.ident _ _ _ _ => mkNode `Lean.Parser.Term.id #[ident, mkNullNode]
| _                    => unreachable!

/--
  Create a simple `Lean.Parser.Term.id` syntax using position
  information from `ref` and name `n`. By simple, we mean that
  `optional (explicitUniv <|> namedPattern)` is none. -/
def mkTermId (ref : Syntax) (n : Name) : Syntax :=
mkTermIdFromIdent (mkIdentFrom ref n)

/--
  Return true if the given syntax is a `Lean.Parser.Term.cdot` or
  is a `Lean.Parser.Term.app` containing a `cdot`.
  We use this function as a filter to skip `expandCDotAux` (the expensive part)
  at `expandCDot?` -/
private partial def hasCDot : Syntax → Bool
| stx =>
  match_syntax stx with
  | `(·)     => true
  | `($f $a) => hasCDot f || hasCDot a
  | _        => false

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
  Auxiliary function for expanding `·`s occurring as arguments of
  applications (i.e., `Lean.Parser.Term.app` nodes).
  Example: `foo · s` should expand into `foo _a_<idx> s` where
  `_a_<idx>` is a fresh identifier. -/
private partial def expandCDotInApp : Syntax → StateT (Array Syntax) TermElabM Syntax
| n =>
  match_syntax n with
  | `($f $a) => do f ← expandCDotInApp f; a ← expandCDot a; `($f $a)
  | n        => pure n

/--
  Return `some` if succeeded expanding `·` notation occurring in
  the given syntax. Otherwise, return `none`.
  Examples:
  - `· + 1` => `fun _a_1 => _a_1 + 1`
  - `f · · b` => `fun _a_1 _a_2 => f _a_1 _a_2 b` -/
def expandCDot? : Syntax → TermElabM (Option Syntax)
| n@(Syntax.node k args) =>
  if args.any hasCDot then
    if k == `Lean.Parser.Term.app then do
      (newNode, binders) ← (expandCDotInApp n).run #[];
      `(fun $binders* => $newNode)
    else do {
      (args, binders) ← (args.mapM expandCDot).run #[];
      let newNode := Syntax.node k args;
      `(fun $binders* => $newNode)
    }
  else
    pure none
| _ => pure none

private def exceptionToSorry (ref : Syntax) (ex : Elab.Exception) (expectedType? : Option Expr) : TermElabM Expr := do
expectedType : Expr ← match expectedType? with
  | none              => mkFreshTypeMVar ref
  | some expectedType => pure expectedType;
u ← getLevel ref expectedType;
let syntheticSorry := mkApp2 (mkConst `sorryAx [u]) expectedType (mkConst `Bool.true);
unless ex.data.hasSyntheticSorry $ logMessage ex;
pure syntheticSorry

/-- If `mayPostpone == true`, throw `Expection.postpone`. -/
def tryPostpone : TermElabM Unit := do
ctx ← read;
when ctx.mayPostpone $ throw Exception.postpone

/-- If `mayPostpone == true` and `e`'s head is a metavariable, throw `Exception.postpone`. -/
def tryPostponeIfMVar (e : Expr) : TermElabM Unit :=
when e.getAppFn.isMVar $ tryPostpone

private def postponeElabTerm (stx : Syntax) (expectedType? : Option Expr) : TermElabM Expr := do
trace! `Elab.postpone (stx ++ " : " ++ expectedType?);
mvar ← mkFreshExprMVar stx expectedType? MetavarKind.syntheticOpaque;
ctx ← read;
registerSyntheticMVar stx mvar.mvarId! (SyntheticMVarKind.postponed ctx.macroStack);
pure mvar

/--
  Main function for elaborating terms.
  It extracts the elaboration methods from the environment using the node kind.
  Recall that the environment has a mapping from `SyntaxNodeKind` to `TermElab` methods.
  It creates a fresh macro scope for executing the elaboration method.
  All unlogged trace messages produced by the elaboration method are logged using
  the position information at `stx`. If the elaboration method throws an `Exception.error`,
  the error is logged and a synthetic sorry expression is returned.
  If the elaboration throws `Exception.postpone` and `catchExPostpone == true`,
  a new synthetic metavariable of kind `SyntheticMVarKind.postponed` is created, registered,
  and returned.
  The option `catchExPostpone == false` is used to implement `resumeElabTerm`
  to prevent the creation of another synthetic metavariable when resuming the elaboration. -/
def elabTerm (stx : Syntax) (expectedType? : Option Expr) (catchExPostpone := true) : TermElabM Expr :=
withFreshMacroScope $ withNode stx $ fun node => do
  trace! `Elab.step (toString stx);
  s ← get;
  let tables := termElabAttribute.ext.getState s.env;
  let k := node.getKind;
  match tables.find? k with
  | some elab =>
    catch
      (tracingAt stx (elab node expectedType?))
      (fun ex => match ex with
        | Exception.error ex => exceptionToSorry stx ex expectedType?
        | Exception.postpone =>
          if catchExPostpone then do
            /- If `elab` threw `Exception.postpone`, we reset any state modifications.
               For example, we want to make sure pending synthetic metavariables created by `elab` before
               it threw `Exception.postpone` are discarded.
               Note that we are also discarding the trace messages created by `elab`. If we decide to save
               them, we can do by modifying `tracingAt`.

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
  | none      => throwError stx ("elaboration function for '" ++ toString k ++ "' has not been implemented")

/-- Auxiliary function used to implement `synthesizeSyntheticMVars`. -/
private def resumeElabTerm (stx : Syntax) (expectedType? : Option Expr) : TermElabM Expr :=
elabTerm stx expectedType? false

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
  Execute `x` using the given metavariable `LocalContext` and `LocalInstances`.
  The type class resolution cache is flushed when executing `x` if its `LocalInstances` are
  different from the current ones. -/
def withMVarContext {α} (mvarId : MVarId) (x : TermElabM α) : TermElabM α := do
mvarDecl  ← getMVarDecl mvarId;
ctx       ← read;
let needReset := ctx.localInstances == mvarDecl.localInstances;
withLCtx mvarDecl.lctx mvarDecl.localInstances $ resettingSynthInstanceCacheWhen needReset x

/--
  Try to elaborate `stx` that was postponed by an elaboration method using `Expection.postpone`.
  It returns `true` if it succeeded, and `false` otherwise.
  It is used to implement `synthesizeSyntheticMVars`. -/
private def resumePostponed (macroStack : List Syntax) (stx : Syntax) (mvarId : MVarId) : TermElabM Bool := do
withMVarContext mvarId $ do
  catch
    (adaptReader (fun (ctx : Context) => { macroStack := macroStack, .. ctx }) $ do
      mvarDecl     ← getMVarDecl mvarId;
      expectedType ← instantiateMVars stx mvarDecl.type;
      trace! `Elab.postpone.resume (stx ++ " : " ++ expectedType);
      result       ← resumeElabTerm stx expectedType;
      assignExprMVar mvarId result;
      pure true)
    (fun ex => match ex with
      | Exception.postpone => pure false
      | Exception.error ex => do logMessage ex; pure true)

/- Try to synthesize metavariable using type class resolution.
   This method assumes the local context and local instances of `instMVar` coincide
   with the current local context and local instances.
   Return `true` if the instance was synthesized successfully, and `false` if
   the instance contains unassigned metavariables that are blocking the type class
   resolution procedure. -/
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

/--
  Similar to `synthesizeInstMVarCore`, but makes sure that `instMVar` local context and instances
  are used. It also logs any error message produced. -/
private def synthesizePendingInstMVar (ref : Syntax) (instMVar : MVarId) : TermElabM Bool := do
withMVarContext instMVar $ catch
  (synthesizeInstMVarCore ref instMVar)
  (fun ex => match ex with
    | Exception.error ex => do logMessage ex; pure true
    | Exception.postpone => unreachable!)

/--
  Return `true` iff `mvarId` is assigned to a term whose the
  head is not a metavariable. We use this method to process `SyntheticMVarKind.withDefault`. -/
private def checkWithDefault (ref : Syntax) (mvarId : MVarId) : TermElabM Bool := do
val ← instantiateMVars ref (mkMVar mvarId);
pure $ !val.getAppFn.isMVar

/-- Try to synthesize the given pending synthetic metavariable. -/
private def synthesizeSyntheticMVar (mvarSyntheticDecl : SyntheticMVarDecl) : TermElabM Bool :=
match mvarSyntheticDecl.kind with
| SyntheticMVarKind.typeClass              => synthesizePendingInstMVar mvarSyntheticDecl.ref mvarSyntheticDecl.mvarId
| SyntheticMVarKind.withDefault defaultVal => checkWithDefault mvarSyntheticDecl.ref mvarSyntheticDecl.mvarId
| SyntheticMVarKind.postponed macroStack   => resumePostponed macroStack mvarSyntheticDecl.ref mvarSyntheticDecl.mvarId
| SyntheticMVarKind.tactic tacticCode      => throwError tacticCode "not implemented yet"

/--
  Try to synthesize the current list of pending synthetic metavariables.
  Return `true` if it managed to synthesize at least one of them. -/
private def synthesizeSyntheticMVarsStep : TermElabM Bool := do
s ← get;
let syntheticMVars    := s.syntheticMVars.reverse;
let numSyntheticMVars := syntheticMVars.length;
modify $ fun s => { syntheticMVars := [], .. s };
remainingSyntheticMVars ← syntheticMVars.filterRevM $ fun mvarDecl => not <$> synthesizeSyntheticMVar mvarDecl;
modify $ fun s => { syntheticMVars := s.syntheticMVars ++ remainingSyntheticMVars, .. s };
pure $ numSyntheticMVars != remainingSyntheticMVars.length

/-- Apply default value to any pending synthetic metavariable of kinf `SyntheticMVarKind.withDefault` -/
def synthesizeUsingDefault : TermElabM Bool := do
s ← get;
let len := s.syntheticMVars.length;
newSyntheticMVars ← s.syntheticMVars.filterM $ fun mvarDecl =>
  match mvarDecl.kind with
  | SyntheticMVarKind.withDefault defaultVal => do
      val ← instantiateMVars mvarDecl.ref (mkMVar mvarDecl.mvarId);
      when val.getAppFn.isMVar $
        unlessM (isDefEq mvarDecl.ref val defaultVal) $
          throwError mvarDecl.ref "failed to assign default value to metavariable"; -- TODO: better error message
      pure false
  | _ => pure true;
modify $ fun s => { syntheticMVars := newSyntheticMVars, .. s };
pure $ newSyntheticMVars.length != len

/-- Report an error for each synthetic metavariable that could not be resolved. -/
private def reportStuckSyntheticMVars : TermElabM Unit := do
s ← get;
s.syntheticMVars.forM $ fun mvarSyntheticDecl =>
  match mvarSyntheticDecl.kind with
  | SyntheticMVarKind.typeClass =>
    withMVarContext mvarSyntheticDecl.mvarId $ do
      mvarDecl ← getMVarDecl mvarSyntheticDecl.mvarId;
      logError mvarSyntheticDecl.ref $
        "failed to create type class instance for " ++ indentExpr mvarDecl.type
  | _ => unreachable! -- TODO handle other cases.

/--
  Main loop for `synthesizeSyntheticMVars.
  It keeps executing `synthesizeSyntheticMVarsStep` while progress is being made.
  If `mayPostpone == false`, then it applies default values to `SyntheticMVarKind.withDefault`
  metavariables that are still unresolved, and then tries to resolve metavariables
  with `mayPostpone == false`. That is, we force them to produce error messages and/or commit to
  a "best option". If after that, we still haven't made progress, we report "stuck" errors. -/
private partial def synthesizeSyntheticMVarsAux (mayPostpone := true) : Unit → TermElabM Unit
| _ => do
  s ← get;
  if s.syntheticMVars.isEmpty then pure ()
  else do
    progress ← synthesizeSyntheticMVarsStep;
    if progress then synthesizeSyntheticMVarsAux ()
    else if mayPostpone then pure ()
    else condM synthesizeUsingDefault (synthesizeSyntheticMVarsAux ()) $ do
      progress ← withoutPostponing synthesizeSyntheticMVarsStep;
      if progress then synthesizeSyntheticMVarsAux ()
      else reportStuckSyntheticMVars

/--
  Try to process pending synthetic metavariables. If `mayPostpone == false`,
  then `syntheticMVars` is `[]` after executing this method.  -/
def synthesizeSyntheticMVars (mayPostpone := true) : TermElabM Unit :=
synthesizeSyntheticMVarsAux mayPostpone ()

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
fun stx expectedType? => mkFreshExprMVar stx.val expectedType?

def mkFreshId : TermElabM Name := do
s ← get;
let id := s.ngen.curr;
modify $ fun s => { ngen := s.ngen.next, .. s };
pure id

/--
  If `expectedType?` is `some t`, then ensure `t` and `eType` are definitionally equal.
  If they are not, then try coercions. -/
def ensureHasType (ref : Syntax) (expectedType? : Option Expr) (eType : Expr) (e : Expr) : TermElabM Expr :=
match expectedType? with
| none              => pure e
| some expectedType =>
  condM (isDefEq ref eType expectedType)
    (pure e)
    (do -- TODO try `HasCoe`
        e ← instantiateMVars ref e;
        eType ← instantiateMVars ref eType;
        expectedType ← instantiateMVars ref expectedType;
        let msg : MessageData :=
          "type mismatch" ++ indentExpr e
          ++ Format.line ++ "has type" ++ indentExpr eType
          ++ Format.line ++ "but it is expected to have type" ++ indentExpr expectedType;
        throwError ref msg)

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
| some stx' => withMacroExpansion stx (elabTerm stx' expectedType?)
| none      => elabTerm stx expectedType?

@[builtinTermElab paren] def elabParen : TermElab :=
fun stx expectedType? =>
  let ref := stx.val;
  match_syntax ref with
  | `(())             => pure $ Lean.mkConst `Unit.unit
  | `(($e : $type)) => do
    type ← elabType type;
    e ← elabCDot e expectedType?;
    eType ← inferType ref e;
    ensureHasType ref type eType e
  | `(($e))          => elabCDot e expectedType?
  | `(($e, $es*))   => do
    pairs ← mkPairs (#[e] ++ es.getEvenElems);
    withMacroExpansion stx.val (elabTerm pairs expectedType?)
  | _ => throwError stx.val "unexpected parentheses notation"

@[builtinTermElab «listLit»] def elabListLit : TermElab :=
fun stx expectedType? => do
  let openBkt  := stx.getArg 0;
  let args     := stx.getArg 1;
  let closeBkt := stx.getArg 2;
  let consId   := mkTermId openBkt `List.cons;
  let nilId    := mkTermId closeBkt `List.nil;
  let newStx   := args.foldSepRevArgs (fun arg r => mkAppStx consId #[arg, r]) nilId;
  elabTerm newStx expectedType?

@[builtinTermElab «arrayLit»] def elabArrayLit : TermElab :=
fun stx expectedType? => do
  match_syntax stx.val with
  | `(#[$args*]) => do
    newStx ← `(List.toArray [$args*]);
    withMacroExpansion stx.val (elabTerm newStx expectedType?)
  | _ => throwError stx.val "unexpected array literal syntax"

def elabExplicitUniv (stx : Syntax) : TermElabM (List Level) :=
pure [] -- TODO

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
  (fun result ⟨constName, projs⟩ =>
    catch
      (do const ← mkConst ref constName explicitLevels;
          pure $ (const, projs) :: result)
      (fun _ =>
          -- Remark: we discard candidates based on the number of explicit universe levels provided.
          pure result))
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
    result ← mkConsts ref candidates explicitLevels;
    -- If we had candidates, but `result` is empty, then too many universe levels have been provided
    when result.isEmpty $
      throwError ref ("too many explicit universe levels");
    pure result
  };
  if preresolved.isEmpty then do
    env           ← getEnv;
    currNamespace ← getCurrNamespace;
    openDecls     ← getOpenDecls;
    process (resolveGlobalName env currNamespace openDecls n)
  else
    process preresolved

@[builtinTermElab cdot] def elabBadCDot : TermElab :=
fun stx _ => throwError stx.val "invalid occurrence of `·` notation, it must be surrounded by parentheses (e.g. `(· + 1)`)"

@[builtinTermElab str] def elabStr : TermElab :=
fun stx _ => do
  match (stx.getArg 0).isStrLit? with
  | some val => pure $ mkStrLit val
  | none     => throwError stx.val "ill-formed syntax"

def mkInstMVar (ref : Syntax) (type : Expr) : TermElabM Expr := do
mvar ← mkFreshExprMVar ref type MetavarKind.synthetic;
let mvarId := mvar.mvarId!;
unlessM (synthesizeInstMVarCore ref mvarId) $
  registerSyntheticMVar ref mvarId SyntheticMVarKind.typeClass;
pure mvar

@[builtinTermElab num] def elabNum : TermElab :=
fun stx expectedType? => do
  let ref := stx.val;
  val ← match (stx.getArg 0).isNatLit? with
    | some val => pure (mkNatLit val)
    | none     => throwError stx.val "ill-formed syntax";
  typeMVar ← mkFreshTypeMVar ref MetavarKind.synthetic;
  registerSyntheticMVar ref typeMVar.mvarId! (SyntheticMVarKind.withDefault (Lean.mkConst `Nat));
  match expectedType? with
  | some expectedType => do isDefEq ref expectedType typeMVar; pure ()
  | _                 => pure ();
  u ← getLevel ref typeMVar;
  u ← decLevel ref u;
  mvar ← mkInstMVar ref (mkApp (Lean.mkConst `HasOfNat [u]) typeMVar);
  pure $ mkApp3 (Lean.mkConst `HasOfNat.ofNat [u]) typeMVar mvar val

end Term

@[init] private def regTraceClasses : IO Unit := do
registerTraceClass `Elab.postpone;
pure ()

export Term (TermElabM)

end Elab
end Lean
