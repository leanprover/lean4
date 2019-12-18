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
(univNames       : List Name := [])
(openDecls       : List OpenDecl := [])
(macroStack      : List Syntax := [])
(macroScopeStack : List MacroScope := [0])
(mayPostpone     : Bool := true)

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

abbrev TermElabM := ReaderT Context (EStateM Exception State)
abbrev TermElab  := SyntaxNode → Option Expr → TermElabM Expr

abbrev TermElabResult := EStateM.Result Exception State Expr

instance TermElabM.inhabited {α} : Inhabited (TermElabM α) :=
⟨throw $ arbitrary _⟩

instance TermElabResult.inhabited : Inhabited TermElabResult := ⟨EStateM.Result.ok (arbitrary _) (arbitrary _)⟩

instance TermElabM.MonadQuotation : MonadQuotation TermElabM := {
  getCurrMacroScope := do
    ctx ← read;
    pure ctx.macroScopeStack.head!,
  withFreshMacroScope := fun α x => do
    fresh ← modifyGet (fun st => (st.nextMacroScope, { st with nextMacroScope := st.nextMacroScope + 1 }));
    adaptReader (fun (ctx : Context) => { ctx with macroScopeStack := fresh::ctx.macroScopeStack }) x
}

inductive LVal
| fieldIdx  (i : Nat)
| fieldName (name : String)
| getOp     (idx : Syntax)

instance LVal.hasToString : HasToString LVal :=
⟨fun p => match p with | LVal.fieldIdx i => toString i | LVal.fieldName n => n | LVal.getOp idx => "[" ++ toString idx ++ "]"⟩

/--
  Execute `x`, save resulting expression and new state.
  If `x` fails, then it also stores exception and new state. -/
@[inline] def observing (x : TermElabM Expr) : TermElabM TermElabResult :=
fun ctx s => EStateM.Result.ok (x ctx s) s

def applyResult (result : TermElabResult) : TermElabM Expr :=
match result with
| EStateM.Result.ok e s     => do set s; pure e
| EStateM.Result.error ex s => do set s; throw ex

instance TermElabM.monadLog : MonadLog TermElabM :=
{ getCmdPos   := do ctx ← read; pure ctx.cmdPos,
  getFileMap  := do ctx ← read; pure ctx.fileMap,
  getFileName := do ctx ← read; pure ctx.fileName,
  logMessage  := fun msg => modify $ fun s => { messages := s.messages.add msg, .. s } }

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

private def mkMessageAux (ctx : Context) (ref : Syntax) (msgData : MessageData) (severity : MessageSeverity) : Message :=
mkMessageCore ctx.fileName ctx.fileMap msgData severity (ref.getPos.getD ctx.cmdPos)

private def fromMetaException (ctx : Context) (ref : Syntax) (ex : Meta.Exception) : Exception :=
mkMessageAux ctx ref ex.toMessageData MessageSeverity.error

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
| none      => liftMetaM ref $ do u ← Meta.mkFreshLevelMVar; Meta.mkFreshExprMVar (mkSort u) userName? kind
def getLevel (ref : Syntax) (type : Expr) : TermElabM Level := liftMetaM ref $ Meta.getLevel type
def mkForall (ref : Syntax) (xs : Array Expr) (e : Expr) : TermElabM Expr := liftMetaM ref $ Meta.mkForall xs e
def mkLambda (ref : Syntax) (xs : Array Expr) (e : Expr) : TermElabM Expr := liftMetaM ref $ Meta.mkLambda xs e
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

def registerSyntheticMVar (ref : Syntax) (mvarId : MVarId) (kind : SyntheticMVarKind) : TermElabM Unit :=
modify $ fun s => { syntheticMVars := { mvarId := mvarId, ref := ref, kind := kind } :: s.syntheticMVars, .. s }

@[inline] def withoutPostponing {α} (x : TermElabM α) : TermElabM α :=
adaptReader (fun (ctx : Context) => { mayPostpone := false, .. ctx }) x

@[inline] def withNode {α} (stx : Syntax) (x : SyntaxNode → TermElabM α) : TermElabM α :=
stx.ifNode x (fun _ => throwError stx "term elaborator failed, unexpected syntax")

@[inline] def tracingAtPos {α} (pos : String.Pos) (x : TermElabM α) : TermElabM α := do
oldTraceState ← getTraceState;
setTraceState {};
finally x $ do
  traceState ← getTraceState;
  traceState.traces.forM $ logInfoAt pos;
  setTraceState oldTraceState

@[inline] def tracingAt {α} (ref : Syntax) (x : TermElabM α) : TermElabM α := do
ctx ← read;
tracingAtPos (ref.getPos.getD ctx.cmdPos) x

def mkExplicitBinder (n : Syntax) (type : Syntax) : Syntax :=
mkNode `Lean.Parser.Term.explicitBinder #[mkAtom "(", mkNullNode #[n], mkNullNode #[mkAtom ":", type], mkNullNode, mkAtom ")"]

private def mkFreshAnonymousName : TermElabM Name := do
s ← get;
let anonymousIdx := s.anonymousIdx;
modify $ fun s => { anonymousIdx := s.anonymousIdx + 1, .. s};
pure $ (`_a).appendIndexAfter anonymousIdx

private def mkFreshAnonymousIdent (ref : Syntax) : TermElabM Syntax := do
n ← mkFreshAnonymousName;
pure $ mkIdentFrom ref n

private def mkFreshInstanceName : TermElabM Name := do
s ← get;
let instIdx := s.instImplicitIdx;
modify $ fun s => { instImplicitIdx := s.instImplicitIdx + 1, .. s};
pure $ (`_inst).appendIndexAfter instIdx

def mkHole := mkNode `Lean.Parser.Term.hole #[mkAtom "_"]

def mkTermIdFromIdent (ident : Syntax) : Syntax :=
mkNode `Lean.Parser.Term.id #[ident, mkNullNode]

def mkTermId (ref : Syntax) (n : Name) : Syntax :=
mkTermIdFromIdent (mkIdentFrom ref n)

def exceptionToSorry (ref : Syntax) (ex : Exception) (expectedType? : Option Expr) : TermElabM Expr := do
expectedType : Expr ← match expectedType? with
  | none              => mkFreshExprMVar ref
  | some expectedType => pure expectedType;
u ← getLevel ref expectedType;
let syntheticSorry := mkApp2 (mkConst `sorryAx [u]) expectedType (mkConst `Bool.true);
unless ex.data.hasSyntheticSorry $ logMessage ex;
pure syntheticSorry

partial def hasCDot : Syntax → Bool
| Syntax.node `Lean.Parser.Term.cdot _   => true
| Syntax.node `Lean.Parser.Term.app args => hasCDot (args.getA 0) || hasCDot (args.getA 1)
| _ => false

partial def expandCDotAux : Bool → Syntax → StateT (Array Syntax) TermElabM Syntax
| _, n@(Syntax.node `Lean.Parser.Term.cdot _) => do
  ident ← liftM $ mkFreshAnonymousIdent n;
  let id := mkTermIdFromIdent ident;
  modify $ fun s => s.push id;
  pure id
| false, n@(Syntax.node `Lean.Parser.Term.app args) =>
  if args.size == 2 then do
    a1 ← expandCDotAux false $ args.get! 0;
    a2 ← expandCDotAux true  $ args.get! 1;
    pure $ Syntax.node `Lean.Parser.Term.app #[a1, a2]
  else
    pure n
| _, n => pure n

def expandCDotArgs (args : Array Syntax) : StateT (Array Syntax) TermElabM (Array Syntax) :=
args.mapM (expandCDotAux false)

def expandCDot? : Syntax → TermElabM (Option Syntax)
| Syntax.node k args =>
  if args.any hasCDot then do
    (args, binders) ← (expandCDotArgs args).run #[];
    let newNode := Syntax.node k args;
    result ← `(fun $binders* => $newNode);
    pure result
  else
    pure none
| _ => pure none

def elabTerm (stx : Syntax) (expectedType? : Option Expr) : TermElabM Expr :=
withFreshMacroScope $ withNode stx $ fun node => do
  trace! `Elab.step (toString stx);
  s ← get;
  let tables := termElabAttribute.ext.getState s.env;
  let k := node.getKind;
  match tables.find? k with
  | some elab =>
    catch
      (tracingAt stx (elab node expectedType?))
      (fun ex => exceptionToSorry stx ex expectedType?)
  | none      => throwError stx ("elaboration function for '" ++ toString k ++ "' has not been implemented")

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

def elabType (stx : Syntax) : TermElabM Expr := do
u ← mkFreshLevelMVar stx;
type ← elabTerm stx (mkSort u);
ensureType stx type

@[builtinTermElab «prop»] def elabProp : TermElab :=
fun _ _ => pure $ mkSort levelZero

@[builtinTermElab «sort»] def elabSort : TermElab :=
fun _ _ => pure $ mkSort levelZero

@[builtinTermElab «type»] def elabTypeStx : TermElab :=
fun _ _ => pure $ mkSort levelOne

@[builtinTermElab «hole»] def elabHole : TermElab :=
fun stx expectedType? => mkFreshExprMVar stx.val expectedType?

/--
  Given syntax of the forms
    a) (`:` term)?
    b) `:` term
  into `term` if it is present, or a hole if not. -/
private def expandBinderType (stx : Syntax) : Syntax :=
if stx.getNumArgs == 0 then
  mkHole
else
  stx.getArg 1

/-- Given syntax of the form `ident <|> hole`, return `ident`. If `hole`, then we create a new anonymous name. -/
private def expandBinderIdent (stx : Syntax) : TermElabM Syntax :=
if stx.getKind == `Lean.Parser.Term.hole then do
  mkFreshAnonymousIdent stx
else
  pure stx

/-- Given syntax of the form `(ident >> " : ")?`, return `ident`, or a new instance name. -/
private def expandOptIdent (stx : Syntax) : TermElabM Syntax :=
if stx.getNumArgs == 0 then do
  id ← mkFreshInstanceName; pure $ mkIdentFrom stx id
else
  pure $ stx.getArg 0

structure BinderView :=
(id : Syntax) (type : Syntax) (bi : BinderInfo)

private def matchBinder (stx : Syntax) : TermElabM (Array BinderView) :=
withNode stx $ fun node => do
  let k := node.getKind;
  if k == `Lean.Parser.Term.simpleBinder then
    -- binderIdent+
    let ids  := (node.getArg 0).getArgs;
    let type := mkHole;
    ids.mapM $ fun id => do id ← expandBinderIdent id; pure { id := id, type := type, bi := BinderInfo.default }
  else if k == `Lean.Parser.Term.explicitBinder then
    -- `(` binderIdent+ binderType (binderDefault <|> binderTactic)? `)`
    let ids  := (node.getArg 1).getArgs;
    let type := expandBinderType (node.getArg 2);
    -- TODO handle `binderDefault` and `binderTactic`
    ids.mapM $ fun id => do id ← expandBinderIdent id; pure { id := id, type := type, bi := BinderInfo.default }
  else if k == `Lean.Parser.Term.implicitBinder then
    -- `{` binderIdent+ binderType `}`
    let ids  := (node.getArg 1).getArgs;
    let type := expandBinderType (node.getArg 2);
    ids.mapM $ fun id => do id ← expandBinderIdent id; pure { id := id, type := type, bi := BinderInfo.implicit }
  else if k == `Lean.Parser.Term.instBinder then do
    -- `[` optIdent type `]`
    id ← expandOptIdent (node.getArg 1);
    let type := node.getArg 2;
    pure #[ { id := id, type := type, bi := BinderInfo.instImplicit } ]
  else
    throwError stx "term elaborator failed, unexpected binder syntax"

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

def mkFreshId : TermElabM Name := do
s ← get;
let id := s.ngen.curr;
modify $ fun s => { ngen := s.ngen.next, .. s };
pure id

private partial def elabBinderViews (binderViews : Array BinderView)
    : Nat → Array Expr → LocalContext → LocalInstances → TermElabM (Array Expr × LocalContext × LocalInstances)
| i, fvars, lctx, localInsts =>
  if h : i < binderViews.size then
    let binderView := binderViews.get ⟨i, h⟩;
    withLCtx lctx localInsts $ do
      type       ← elabType binderView.type;
      fvarId     ← mkFreshId;
      let fvar  := mkFVar fvarId;
      let fvars := fvars.push fvar;
      -- dbgTrace (toString binderView.id.getId ++ " : " ++ toString type);
      let lctx  := lctx.mkLocalDecl fvarId binderView.id.getId type binderView.bi;
      className? ← isClass binderView.type type;
      match className? with
      | none           => elabBinderViews (i+1) fvars lctx localInsts
      | some className => do
        resetSynthInstanceCache;
        let localInsts := localInsts.push { className := className, fvar := mkFVar fvarId };
        elabBinderViews (i+1) fvars lctx localInsts
  else
    pure (fvars, lctx, localInsts)

private partial def elabBindersAux (binders : Array Syntax)
    : Nat → Array Expr → LocalContext → LocalInstances → TermElabM (Array Expr × LocalContext × LocalInstances)
| i, fvars, lctx, localInsts =>
  if h : i < binders.size then do
    binderViews ← matchBinder (binders.get ⟨i, h⟩);
    (fvars, lctx, localInsts) ← elabBinderViews binderViews 0 fvars lctx localInsts;
    elabBindersAux (i+1) fvars lctx localInsts
  else
    pure (fvars, lctx, localInsts)

@[inline] def elabBinders {α} (binders : Array Syntax) (x : Array Expr → TermElabM α) : TermElabM α := do
lctx ← getLCtx;
localInsts ← getLocalInsts;
(fvars, lctx, newLocalInsts) ← elabBindersAux binders 0 #[] lctx localInsts;
resettingSynthInstanceCacheWhen (newLocalInsts.size > localInsts.size) $
  adaptReader (fun (ctx : Context) => { lctx := lctx, localInstances := newLocalInsts, .. ctx }) (x fvars)

@[inline] def elabBinder {α} (binder : Syntax) (x : Expr → TermElabM α) : TermElabM α :=
elabBinders #[binder] (fun fvars => x (fvars.get! 1))

@[builtinTermElab «forall»] def elabForall : TermElab :=
fun stx _ =>
  -- `forall` binders+ `,` term
  let binders := (stx.getArg 1).getArgs;
  let term    := stx.getArg 3;
  elabBinders binders $ fun xs => do
    e ← elabType term;
    mkForall stx.val xs e

@[builtinTermElab arrow] def elabArrow : TermElab :=
fun stx expectedType? => do
  id ← mkFreshAnonymousIdent stx.val;
  let dom    := stx.getArg 0;
  let rng    := stx.getArg 2;
  let newStx := mkNode `Lean.Parser.Term.forall #[mkAtom "forall", mkNullNode #[mkExplicitBinder id dom], mkAtom ",", rng];
  elabTerm newStx expectedType?

@[builtinTermElab depArrow] def elabDepArrow : TermElab :=
fun stx _ =>
  -- bracktedBinder `->` term
  let binder := stx.getArg 0;
  let term   := stx.getArg 2;
  elabBinders #[binder] $ fun xs => do
    e ← elabType term;
    mkForall stx.val xs e

/-
  Auxiliary functions for converting `Term.app ... (Term.app id_1 id_2) ... id_n` into #[id_1, ..., id_m]`
  It is used at `expandFunBinders`. -/
partial def getFunBinderIdsAux? : Bool → Syntax → Array Syntax → TermElabM (Option (Array Syntax))
| false, Syntax.node `Lean.Parser.Term.app args, acc => do
  (some acc) ← getFunBinderIdsAux? false (args.getA 0) acc | pure none;
  getFunBinderIdsAux? true (args.getA 1) acc
| _, Syntax.node `Lean.Parser.Term.id args, acc =>
  if (args.getA 1).isNone then
    pure (some (acc.push (args.getA 0)))
  else
    pure none
| _, n@(Syntax.node `Lean.Parser.Term.hole _), acc => do
  ident ← mkFreshAnonymousIdent n;
  pure (some (acc.push ident))
| idOnly, stx, acc => pure none

def getFunBinderIds? (stx : Syntax) : TermElabM (Option (Array Syntax)) :=
getFunBinderIdsAux? false stx #[]

partial def expandFunBindersAux (binders : Array Syntax) : Syntax → Nat → Array Syntax → TermElabM (Array Syntax × Syntax)
| body, i, newBinders =>
  if h : i < binders.size then
    let binder := binders.get ⟨i, h⟩;
    let processAsPattern : Unit → TermElabM (Array Syntax × Syntax) := fun _ => do {
      let pattern := binder;
      ident ← mkFreshAnonymousIdent binder;
      (binders, newBody) ← expandFunBindersAux body (i+1) (newBinders.push $ mkExplicitBinder ident mkHole);
      let major := mkTermIdFromIdent ident;
      newBody ← `(match $major with | $pattern => $newBody);
      pure (binders, newBody)
    };
    match binder with
    | Syntax.node `Lean.Parser.Term.id args => do
      unless (args.getA 1).isNone $ throwError binder "invalid binder, simple identifier expected";
      let ident := args.getA 0;
      let type  := mkHole;
      expandFunBindersAux body (i+1) (newBinders.push $ mkExplicitBinder ident type)
    | Syntax.node `Lean.Parser.Term.hole _ => do
      ident ← mkFreshAnonymousIdent binder;
      let type := binder;
      expandFunBindersAux body (i+1) (newBinders.push $ mkExplicitBinder ident type)
    | Syntax.node `Lean.Parser.Term.paren args =>
      -- `(` (termParser >> parenSpecial)? `)`
      -- parenSpecial := (tupleTail <|> typeAscription)?
      let binderBody := binder.getArg 1;
      if binderBody.isNone then processAsPattern ()
      else
        let idents  := binderBody.getArg 0;
        let special := binderBody.getArg 1;
        if special.isNone then processAsPattern ()
        else if (special.getArg 0).getKind != `Lean.Parser.Term.typeAscription then processAsPattern ()
        else do
          -- typeAscription := `:` term
          let type := ((special.getArg 0).getArg 1);
          idents? ← getFunBinderIds? idents;
          match idents? with
          | some idents => expandFunBindersAux body (i+1) (newBinders ++ idents.map (fun ident => mkExplicitBinder ident type))
          | none        => processAsPattern ()
    | _ => processAsPattern ()
  else
    pure (newBinders, body)

def expandFunBinders (binders : Array Syntax) (body : Syntax) : TermElabM (Array Syntax × Syntax) :=
expandFunBindersAux binders body 0 #[]

@[builtinTermElab «fun»] def elabFun : TermElab :=
fun stx expectedType? => do
  -- `fun` term+ `=>` term
  let binders := (stx.getArg 1).getArgs;
  let body := stx.getArg 3;
  (binders, body) ← expandFunBinders binders body;
  elabBinders binders $ fun xs => do
    -- TODO: expected type
    e ← elabTerm body none;
    mkLambda stx.val xs e

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

partial def mkPairsAux (elems : Array Syntax) : Nat → Syntax → TermElabM Syntax
| i, acc =>
  if i > 0 then do
    let i    := i - 1;
    let elem := elems.get! i;
    acc ← `(Prod.mk $elem $acc);
    mkPairsAux i acc
  else
    pure acc

def mkPairs (elems : Array Syntax) : TermElabM Syntax :=
mkPairsAux elems (elems.size - 1) elems.back

def elabCDot (stx : Syntax) (expectedType? : Option Expr) : TermElabM Expr := do
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

def elabExplicitUniv (stx : Syntax) : TermElabM (List Level) :=
pure [] -- TODO

inductive Arg
| stx  (val : Syntax)
| expr (val : Expr)

instance Arg.inhabited : Inhabited Arg := ⟨Arg.stx (arbitrary _)⟩

instance Arg.hasToString : HasToString Arg :=
⟨fun arg => match arg with
  | Arg.stx  val => toString val
  | Arg.expr val => toString val⟩

structure NamedArg :=
(name : Name) (val : Arg)

instance NamedArg.hasToString : HasToString NamedArg :=
⟨fun s => "(" ++ toString s.name ++ " := " ++ toString s.val ++ ")"⟩

instance NamedArg.inhabited : Inhabited NamedArg := ⟨{ name := arbitrary _, val := arbitrary _ }⟩

def addNamedArg (ref : Syntax) (namedArgs : Array NamedArg) (namedArg : NamedArg) : TermElabM (Array NamedArg) := do
when (namedArgs.any $ fun namedArg' => namedArg.name == namedArg'.name) $
  throwError ref ("argument '" ++ toString namedArg.name ++ "' was already set");
pure $ namedArgs.push namedArg

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

/-- Consume parameters of the form `(x : A := val)` and `(x : A . tactic)` -/
def consumeDefaultParams (ref : Syntax) : Expr → Expr → TermElabM Expr
| eType, e =>
  -- TODO
  pure e

def mkInstMVar (ref : Syntax) (type : Expr) : TermElabM Expr := do
mvar ← mkFreshExprMVar ref type MetavarKind.synthetic;
let mvarId := mvar.mvarId!;
registerSyntheticMVar ref mvarId SyntheticMVarKind.typeClass;
pure mvar

def synthesizeInstMVar (ref : Syntax) (instMVar : MVarId) : TermElabM Unit :=
condM (isExprMVarAssigned instMVar) (pure ()) $ do
  instMVarDecl ← getMVarDecl instMVar;
  let type := instMVarDecl.type;
  type ← instantiateMVars ref type;
  result ← trySynthInstance ref type;
  match result with
  | LOption.some val => assignExprMVar instMVar val
  | LOption.undef    => pure () -- we will try later
  | LOption.none     => throwError ref ("failed to synthesize instance" ++ indentExpr type)

def synthesizeInstMVars (ref : Syntax) (instMVars : Array MVarId) : TermElabM Unit :=
instMVars.forM $ synthesizeInstMVar ref

private def elabArg (ref : Syntax) (arg : Arg) (expectedType : Expr) : TermElabM Expr :=
match arg with
| Arg.expr val => do
  valType ← inferType ref val;
  ensureHasType ref expectedType valType val
| Arg.stx val  => do
  val ← elabTerm val expectedType;
  valType ← inferType ref val;
  ensureHasType ref expectedType valType val

private partial def elabAppArgsAux (ref : Syntax) (args : Array Arg) (expectedType? : Option Expr) (explicit : Bool)
    : Nat → Array NamedArg → Array MVarId → Expr → Expr → TermElabM Expr
| argIdx, namedArgs, instMVars, eType, e => do
  let finalize : Unit → TermElabM Expr := fun _ => do {
    -- all user explicit arguments have been consumed
    e ← if explicit then pure e else consumeDefaultParams ref eType e;
    e ← ensureHasType ref expectedType? eType e;
    synthesizeInstMVars ref instMVars;
    pure e
  };
  eType ← whnfForall ref eType;
  match eType with
  | Expr.forallE n d b c =>
    match namedArgs.findIdx? (fun namedArg => namedArg.name == n) with
    | some idx => do
      let arg := namedArgs.get! idx;
      let namedArgs := namedArgs.eraseIdx idx;
      argElab ← elabArg ref arg.val d;
      elabAppArgsAux argIdx namedArgs instMVars (b.instantiate1 argElab) (mkApp e argElab)
    | none =>
      let processExplictArg : Unit → TermElabM Expr := fun _ => do {
        if h : argIdx < args.size then do
          argElab ← elabArg ref (args.get ⟨argIdx, h⟩) d;
          elabAppArgsAux (argIdx + 1) namedArgs instMVars (b.instantiate1 argElab) (mkApp e argElab)
        else if namedArgs.isEmpty then
          finalize ()
        else
          throwError ref ("explicit parameter '" ++ n ++ "' is missing, unused named arguments " ++ toString (namedArgs.map $ fun narg => narg.name))
      };
      if explicit then
        processExplictArg ()
      else match c.binderInfo with
        | BinderInfo.implicit => do
          a ← mkFreshExprMVar ref d;
          elabAppArgsAux argIdx namedArgs instMVars (b.instantiate1 a) (mkApp e a)
        | BinderInfo.instImplicit => do
          a ← mkInstMVar ref d;
          elabAppArgsAux argIdx namedArgs (instMVars.push a.mvarId!) (b.instantiate1 a) (mkApp e a)
        | _ =>
          processExplictArg ()
  | _ =>
    if namedArgs.isEmpty && argIdx == args.size then
      finalize ()
    else
      -- TODO: try `HasCoeToFun`
      throwError ref "too many arguments"

private def elabAppArgs (ref : Syntax) (f : Expr) (namedArgs : Array NamedArg) (args : Array Arg)
    (expectedType? : Option Expr) (explicit : Bool) : TermElabM Expr := do
fType ← inferType ref f;
let argIdx    := 0;
let instMVars := #[];
elabAppArgsAux ref args expectedType? explicit argIdx namedArgs instMVars fType f

inductive LValResolution
| projFn   (baseStructName : Name) (structName : Name) (fieldName : Name)
| projIdx  (structName : Name) (idx : Nat)
| const    (baseName : Name) (constName : Name)
| localRec (baseName : Name) (fullName : Name) (fvar : Expr)
| getOp    (fullName : Name) (idx : Syntax)

private def throwLValError {α} (ref : Syntax) (e : Expr) (eType : Expr) (msg : MessageData) : TermElabM α :=
throwError ref $ msg ++ indentExpr e ++ Format.line ++ "has type" ++ indentExpr eType

private def resolveLValAux (ref : Syntax) (e : Expr) (eType : Expr) (lval : LVal) : TermElabM LValResolution :=
match eType.getAppFn, lval with
| Expr.const structName _ _, LVal.fieldIdx idx => do
  when (idx == 0) $
    throwError ref "invalid projection, index must be greater than 0";
  env ← getEnv;
  unless (isStructureLike env structName) $
    throwLValError ref e eType "invalid projection, structure expected";
  let fieldNames := getStructureFields env structName;
  if h : idx - 1 < fieldNames.size then
    if isStructure env structName then
      pure $ LValResolution.projFn structName structName (fieldNames.get ⟨idx - 1, h⟩)
    else
      /- `structName` was declared using `inductive` command.
         So, we don't projection functions for it. Thus, we use `Expr.proj` -/
      pure $ LValResolution.projIdx structName (idx - 1)
  else
    throwLValError ref e eType ("invalid projection, structure has only " ++ toString fieldNames.size ++ " field(s)")
| Expr.const structName _ _, LVal.fieldName fieldName => do
  env ← getEnv;
  let searchEnv (fullName : Name) : TermElabM LValResolution := do {
    match env.find? fullName with
    | some _ => pure $ LValResolution.const structName fullName
    | none   => throwLValError ref e eType $
      "invalid field notation, '" ++ fieldName ++ "' is not a valid \"field\" because environment does not contain '" ++ fullName ++ "'"
  };
  let searchLCtx : Unit → TermElabM LValResolution := fun _ => do {
    let fullName := structName ++ fieldName;
    currNamespace ← getCurrNamespace;
    let localName := fullName.replacePrefix currNamespace Name.anonymous;
    lctx ← getLCtx;
    match lctx.findFromUserName? localName with
    | some localDecl =>
      if localDecl.binderInfo == BinderInfo.auxDecl then
        /- LVal notation is being used to make a "local" recursive call. -/
        pure $ LValResolution.localRec structName fullName localDecl.toExpr
      else
        searchEnv fullName
    | none => searchEnv fullName
  };
  if isStructure env structName then
    match findField? env structName fieldName with
    | some baseStructName => pure $ LValResolution.projFn baseStructName structName fieldName
    | none                => searchLCtx ()
  else
    searchLCtx ()
| Expr.const structName _ _, LVal.getOp idx => do
  env ← getEnv;
  let fullName := mkNameStr structName "getOp";
  match env.find? fullName with
  | some _ => pure $ LValResolution.getOp fullName idx
  | none   => throwLValError ref e eType $ "invalid [..] notation because environment does not contain '" ++ fullName ++ "'"
| _, LVal.getOp idx =>
  throwLValError ref e eType "invalid [..] notation, type is not of the form (C ...) where C is a constant"
| _, _ =>
  throwLValError ref e eType "invalid field notation, type is not of the form (C ...) where C is a constant"

private partial def resolveLValLoop (ref : Syntax) (e : Expr) (lval : LVal) : Expr → Array Exception → TermElabM LValResolution
| eType, previousExceptions => do
  eType ← whnfCore ref eType;
  -- If eType is metavariable, we must interrupt and postpone
  catch (resolveLValAux ref e eType lval)
    (fun ex => do
      eType? ← unfoldDefinition? ref eType;
      match eType? with
      | some eType => resolveLValLoop eType (previousExceptions.push ex)
      | none => do
        previousExceptions.forM $ fun ex => logMessage ex;
        throw ex)

private def resolveLVal (ref : Syntax) (e : Expr) (lval : LVal) : TermElabM LValResolution := do
eType ← inferType ref e;
resolveLValLoop ref e lval eType #[]

private partial def mkBaseProjections (ref : Syntax) (baseStructName : Name) (structName : Name) (e : Expr) : TermElabM Expr := do
env ← getEnv;
match getPathToBaseStructure? env baseStructName structName with
| none => throwError ref "failed to access field in parent structure"
| some path =>
  path.foldlM
    (fun e projFunName => do
      projFn ← mkConst ref projFunName;
      elabAppArgs ref projFn #[{ name := `self, val := Arg.expr e }] #[] none false)
    e

/- Auxiliary method for field notation. It tries to add `e` to `args` as the first explicit parameter
   which takes an element of type `(C ...)` where `C` is `baseName`.
   `fullName` is the name of the resolved "field" access function. It is used for reporting errors -/
private def addLValArg (ref : Syntax) (baseName : Name) (fullName : Name) (e : Expr) (args : Array Arg) : Nat → Expr → TermElabM (Array Arg)
| i, Expr.forallE _ d b c =>
  if !c.binderInfo.isExplicit then
    addLValArg i b
  else if d.isAppOf baseName then
    pure $ args.insertAt i (Arg.expr e)
  else if i < args.size then
    addLValArg (i+1) b
  else
    throwError ref $ "invalid field notation, insufficient number of arguments for '" ++ fullName ++ "'"
| _, fType =>
  throwError ref $
    "invalid field notation, function '" ++ fullName ++ "' does not have explicit argument with type (" ++ baseName ++ " ...)"

private def elabAppLValsAux (ref : Syntax) (namedArgs : Array NamedArg) (args : Array Arg) (expectedType? : Option Expr) (explicit : Bool)
    : Expr → List LVal → TermElabM Expr
| f, []            => elabAppArgs ref f namedArgs args expectedType? explicit
| f, lval::lvals => do
  lvalRes ← resolveLVal ref f lval;
  match lvalRes with
  | LValResolution.projIdx structName idx =>
    let f := mkProj structName idx f;
    elabAppLValsAux f lvals
  | LValResolution.projFn baseStructName structName fieldName => do
    f ← mkBaseProjections ref baseStructName structName f;
    projFn ← mkConst ref (baseStructName ++ fieldName);
    if lvals.isEmpty then do
      namedArgs ← addNamedArg ref namedArgs { name := `self, val := Arg.expr f };
      elabAppArgs ref projFn namedArgs args expectedType? explicit
    else do
      f ← elabAppArgs ref projFn #[{ name := `self, val := Arg.expr f }] #[] none false;
      elabAppLValsAux f lvals
  | LValResolution.const baseName constName => do
    projFn ← mkConst ref constName;
    if lvals.isEmpty then do
      projFnType ← inferType ref projFn;
      args ← addLValArg ref baseName constName f args 0 projFnType;
      elabAppArgs ref projFn namedArgs args expectedType? explicit
    else do
      f ← elabAppArgs ref projFn #[] #[Arg.expr f] none false;
      elabAppLValsAux f lvals
  | LValResolution.localRec baseName fullName fvar =>
    if lvals.isEmpty then do
      fvarType ← inferType ref fvar;
      args ← addLValArg ref baseName fullName f args 0 fvarType;
      elabAppArgs ref fvar namedArgs args expectedType? explicit
    else do
      f ← elabAppArgs ref fvar #[] #[Arg.expr f] none false;
      elabAppLValsAux f lvals
  | LValResolution.getOp fullName idx => do
    getOpFn ← mkConst ref fullName;
    if lvals.isEmpty then do
      namedArgs ← addNamedArg ref namedArgs { name := `self, val := Arg.expr f };
      namedArgs ← addNamedArg ref namedArgs { name := `idx, val := Arg.stx idx };
      elabAppArgs ref getOpFn namedArgs args expectedType? explicit
    else do
      f ← elabAppArgs ref getOpFn #[{ name := `self, val := Arg.expr f }, { name := `idx, val := Arg.stx idx }] #[] none false;
      elabAppLValsAux f lvals

private def elabAppLVals (ref : Syntax) (f : Expr) (lvals : List LVal) (namedArgs : Array NamedArg) (args : Array Arg)
    (expectedType? : Option Expr) (explicit : Bool) : TermElabM Expr := do
when (!lvals.isEmpty && explicit) $ throwError ref "invalid use of field notation with `@` modifier";
elabAppLValsAux ref namedArgs args expectedType? explicit f lvals

private partial def elabAppFn (ref : Syntax) : Syntax → List LVal → Array NamedArg → Array Arg → Option Expr → Bool → Array TermElabResult → TermElabM (Array TermElabResult)
| f, lvals, namedArgs, args, expectedType?, explicit, acc =>
  let k := f.getKind;
  if k == `Lean.Parser.Term.explicit then
    -- `f` is of the form `@ id`
    elabAppFn (f.getArg 1) lvals namedArgs args expectedType? true acc
  else if k == choiceKind then
    f.getArgs.foldlM (fun acc f => elabAppFn f lvals namedArgs args expectedType? explicit acc) acc
  else if k == `Lean.Parser.Term.proj then
    -- term `.` (fieldIdx <|> ident)
    let field := f.getArg 2;
    match field.isFieldIdx?, field with
    | some idx, _                      => elabAppFn (f.getArg 0) (LVal.fieldIdx idx :: lvals) namedArgs args expectedType? explicit acc
    | _,        Syntax.ident _ _ val _ =>
      let newLVals := val.components.map (fun n => LVal.fieldName (toString n));
      elabAppFn (f.getArg 0) (newLVals ++ lvals) namedArgs args expectedType? explicit acc
    | _,        _                      => throwError field "unexpected kind of field access"
  else if k == `Lean.Parser.Term.arrayRef then do
    -- term `[` term `]`
    let idx := f.getArg 2;
    elabAppFn (f.getArg 0) (LVal.getOp idx :: lvals) namedArgs args expectedType? explicit acc
  else if k == `Lean.Parser.Term.id then
    -- ident (explicitUniv | namedPattern)?
    -- Remark: `namedPattern` should already have been expanded
    match f.getArg 0 with
    | Syntax.ident _ _ n preresolved => do
      us        ← elabExplicitUniv (f.getArg 1);
      funLVals ← resolveName f n preresolved us;
      funLVals.foldlM
        (fun acc ⟨f, fields⟩ => do
          let lvals' := fields.map LVal.fieldName;
          s ← observing $ elabAppLVals ref f (lvals' ++ lvals) namedArgs args expectedType? explicit;
          pure $ acc.push s)
        acc
    | _ => unreachable!
  else do
    f ← withoutPostponing $ elabTerm f none;
    s ← observing $ elabAppLVals ref f lvals namedArgs args expectedType? explicit;
    pure $ acc.push s

private def getSuccess (candidates : Array TermElabResult) : Array TermElabResult :=
candidates.filter $ fun c => match c with
  | EStateM.Result.ok _ _ => true
  | _ => false

private def toMessageData (msg : Message) (stx : Syntax) : TermElabM MessageData := do
strPos ← getPos stx;
pos ← getPosition strPos;
if pos == msg.pos then
  pure msg.data
else
  pure $ toString msg.pos.line ++ ":" ++ toString msg.pos.column ++ " " ++ msg.data

private def mergeFailures {α} (failures : Array TermElabResult) (stx : Syntax) : TermElabM α := do
msgs ← failures.mapM $ fun failure =>
  match failure with
  | EStateM.Result.ok _ _     => unreachable!
  | EStateM.Result.error ex s => toMessageData ex stx;
throwError stx ("overloaded, errors " ++ MessageData.ofArray msgs)

private def elabAppAux (ref : Syntax) (f : Syntax) (namedArgs : Array NamedArg) (args : Array Arg) (expectedType? : Option Expr) : TermElabM Expr := do
/- TODO: if `f` contains `choice` or overloaded symbols, `mayPostpone == true`, and `expectedType? == some ?m` where `?m` is not assigned,
   then we should postpone until `?m` is assigned.
   Another (more expensive) option is: execute, and if successes > 1, `mayPostpone == true`, and `expectedType? == some ?m` where `?m` is not assigned,
   then we postpone `elabAppAux`. It is more expensive because we would have to re-elaborate the whole thing after we assign `?m`.
   We **can't** continue from `TermElabResult` since they contain a snapshot of the state, and state has changed. -/
candidates ← elabAppFn ref f [] namedArgs args expectedType? false #[];
if candidates.size == 1 then
  applyResult $ candidates.get! 0
else
  let successes := getSuccess candidates;
  if successes.size == 1 then
    applyResult $ successes.get! 0
  else if successes.size > 1 then do
    lctx ← getLCtx;
    let msgs : Array MessageData := successes.map $ fun success => match success with
      | EStateM.Result.ok e s => MessageData.context s.env s.mctx lctx e
      | _                     => unreachable!;
    throwError f ("ambiguous, possible interpretations " ++ MessageData.ofArray msgs)
  else
    mergeFailures candidates f

private partial def expandAppAux : Syntax → Array Syntax → Syntax × Array Syntax
| stx, args => stx.ifNodeKind `Lean.Parser.Term.app
  (fun node =>
    let fn  := node.getArg 0;
    let arg := node.getArg 1;
    expandAppAux fn (args.push arg))
  (fun _ => (stx, args.reverse))

private def expandApp (stx : Syntax) : TermElabM (Syntax × Array NamedArg × Array Arg) := do
let (f, args) := expandAppAux stx #[];
(namedArgs, args) ← args.foldlM
  (fun (acc : Array NamedArg × Array Arg) arg =>
    let (namedArgs, args) := acc;
    arg.ifNodeKind `Lean.Parser.Term.namedArgument
      (fun argNode => do
        -- `(` ident `:=` term `)`
        namedArgs ← addNamedArg arg acc.1 { name := argNode.getIdAt 1, val := Arg.stx $ argNode.getArg 3 };
        pure (namedArgs, args))
      (fun _ =>
        pure (namedArgs, args.push $ Arg.stx arg)))
  (#[], #[]);
pure (f, namedArgs, args)

@[builtinTermElab app] def elabApp : TermElab :=
fun stx expectedType? => do
  (f, namedArgs, args) ← expandApp stx.val;
  elabAppAux stx.val f namedArgs args expectedType?

@[builtinTermElab «id»] def elabId : TermElab := elabApp
@[builtinTermElab explicit] def elabExplicit : TermElab := elabApp
@[builtinTermElab choice] def elabChoice : TermElab := elabApp
@[builtinTermElab proj] def elabProj : TermElab := elabApp
@[builtinTermElab arrayRef] def elabArrayRef : TermElab := elabApp
@[builtinTermElab cdot] def elabBadCDot : TermElab :=
fun stx _ => throwError stx.val "invalid occurrence of `·` notation, it must be surrounded by parentheses (e.g. `(· + 1)`)"

@[builtinTermElab str] def elabStr : TermElab :=
fun stx _ => do
  match (stx.getArg 0).isStrLit? with
  | some val => pure $ mkStrLit val
  | none     => throwError stx.val "ill-formed syntax"

@[builtinTermElab num] def elabNum : TermElab :=
fun stx expectedType? => do
  -- TODO: postpone if expectedType? is none or metavariable
  let ref := stx.val;
  val ← match (stx.getArg 0).isNatLit? with
    | some val => pure (mkNatLit val)
    | none     => throwError stx.val "ill-formed syntax";
  expectedType ← match expectedType? with
    | some expectedType => pure expectedType
    | none              => mkFreshExprMVar ref;
  u ← getLevel ref expectedType;
  u ← decLevel ref u;
  mvar ← mkInstMVar ref (mkApp (Lean.mkConst `HasOfNat [u]) expectedType);
  synthesizeInstMVar ref mvar.mvarId!;
  pure $ mkApp3 (Lean.mkConst `HasOfNat.ofNat [u]) expectedType mvar val

end Term

@[init] private def regTraceClasses : IO Unit := do
registerTraceClass `Elab.app;
pure ()

export Term (TermElabM)

end Elab
end Lean
