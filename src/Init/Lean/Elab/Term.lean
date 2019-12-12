/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Lean.Meta
import Init.Lean.Elab.Log
import Init.Lean.Elab.Alias
import Init.Lean.Elab.ResolveName
import Init.Lean.Elab.Quotation

namespace Lean
namespace Elab
namespace Term

structure Context extends Meta.Context :=
(fileName    : String)
(fileMap     : FileMap)
(cmdPos      : String.Pos)
(ns          : Name) -- current Namespace
(univNames   : List Name := [])
(openDecls   : List OpenDecl := [])
(macroStack  : List Syntax := [])
(mayPostpone : Bool := true)

inductive SyntheticMVarKind
| typeClass
| tactic (tacticCode : Syntax)
| postponed (macroStack : List Syntax)

structure SyntheticMVarDecl :=
(mvarId : MVarId) (ref : Syntax) (kind : SyntheticMVarKind)

structure State extends Meta.State :=
(syntheticMVars  : List SyntheticMVarDecl := [])
(messages        : MessageLog := {})
(instImplicitIdx : Nat := 1)
(anonymousIdx    : Nat := 1)

instance State.inhabited : Inhabited State := ⟨{ env := arbitrary _ }⟩

abbrev TermElabM := ReaderT Context (EStateM Exception State)
abbrev TermElab  := SyntaxNode → Option Expr → TermElabM Expr

abbrev TermElabResult := EStateM.Result Exception State Expr

instance TermElabM.inhabited {α} : Inhabited (TermElabM α) :=
⟨throw $ arbitrary _⟩

instance TermElabResult.inhabited : Inhabited TermElabResult := ⟨EStateM.Result.ok (arbitrary _) (arbitrary _)⟩

inductive Projection
| num (fieldIdx  : Nat)
| str (fieldName : String)

instance Projection.hasToString : HasToString Projection :=
⟨fun p => match p with | Projection.num n => toString n | Projection.str s => s⟩

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
   match env.find declName with
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
def getNamespace : TermElabM Name := do ctx ← read; pure ctx.ns
def getOpenDecls : TermElabM (List OpenDecl) := do ctx ← read; pure ctx.openDecls
def getLCtx : TermElabM LocalContext := do ctx ← read; pure ctx.lctx
def getLocalInsts : TermElabM LocalInstances := do ctx ← read; pure ctx.localInstances
def getOptions : TermElabM Options       := do ctx ← read; pure ctx.config.opts
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

def mkMessage (ctx : Context) (ref : Syntax) (msgData : MessageData) (severity : MessageSeverity) : Message :=
mkMessageCore ctx.fileName ctx.fileMap msgData severity (ref.getPos.getD ctx.cmdPos)

def mkException (ctx : Context) (ref : Syntax) (msgData : MessageData) : Exception :=
mkMessage ctx ref msgData MessageSeverity.error

private def fromMetaException (ctx : Context) (ref : Syntax) (ex : Meta.Exception) : Exception :=
mkException ctx ref ex.toMessageData

private def fromMetaState (ref : Syntax) (ctx : Context) (s : State) (newS : Meta.State) (oldTraceState : TraceState) : State :=
let traces   := newS.traceState.traces;
let messages := traces.foldl (fun (messages : MessageLog) trace => messages.add (mkMessage ctx ref trace MessageSeverity.information)) s.messages;
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
def unfoldDefinition (ref : Syntax) (e : Expr) : TermElabM (Option Expr) := liftMetaM ref $ Meta.unfoldDefinition e
def instantiateMVars (ref : Syntax) (e : Expr) : TermElabM Expr := liftMetaM ref $ Meta.instantiateMVars e
def isClass (ref : Syntax) (t : Expr) : TermElabM (Option Name) := liftMetaM ref $ Meta.isClass t
def mkFreshLevelMVar (ref : Syntax) : TermElabM Level := liftMetaM ref $ Meta.mkFreshLevelMVar
def mkFreshExprMVar (ref : Syntax) (type? : Option Expr := none) (synthetic : Bool := false) (userName? : Name := Name.anonymous) : TermElabM Expr :=
match type? with
| some type => liftMetaM ref $ Meta.mkFreshExprMVar type userName? synthetic
| none      => liftMetaM ref $ do u ← Meta.mkFreshLevelMVar; Meta.mkFreshExprMVar (mkSort u) userName? synthetic

def mkForall (ref : Syntax) (xs : Array Expr) (e : Expr) : TermElabM Expr := liftMetaM ref $ Meta.mkForall xs e
def trySynthInstance (ref : Syntax) (type : Expr) : TermElabM (LOption Expr) := liftMetaM ref $ Meta.trySynthInstance type

def registerSyntheticMVar (mvarId : MVarId) (ref : Syntax) (kind : SyntheticMVarKind) : TermElabM Unit :=
modify $ fun s => { syntheticMVars := { mvarId := mvarId, ref := ref, kind := kind } :: s.syntheticMVars, .. s }

def throwError {α} (ref : Syntax) (msgData : MessageData) : TermElabM α := do
ctx ← read; throw $ mkException ctx ref msgData

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

def elabTerm (stx : Syntax) (expectedType? : Option Expr) : TermElabM Expr :=
withNode stx $ fun node => do
  trace! `Elab.step (toString stx);
  s ← get;
  let tables := termElabAttribute.ext.getState s.env;
  let k := node.getKind;
  match tables.find k with
  | some elab => tracingAt stx (elab node expectedType?)
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

@[builtinTermElab stxQuot] def elabStxQuot : TermElab :=
fun stx expectedType? => do
  env ← getEnv;
  elabTerm (stxQuot.expand env (stx.getArg 1)) expectedType?

private def mkFreshAnonymousName : TermElabM Name := do
s ← get;
let anonymousIdx := s.anonymousIdx;
modify $ fun s => { anonymousIdx := s.anonymousIdx + 1, .. s};
pure $ (`_a).appendIndexAfter anonymousIdx

private def mkFreshInstanceName : TermElabM Name := do
s ← get;
let instIdx := s.instImplicitIdx;
modify $ fun s => { instImplicitIdx := s.instImplicitIdx + 1, .. s};
pure $ (`_inst).appendIndexAfter instIdx

def mkHole := mkNode `Lean.Parser.Term.hole #[mkAtom "_"]

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
  id ← mkFreshAnonymousName;
  pure $ mkIdentFrom stx id
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

def mkExplicitBinder (n : Syntax) (type : Syntax) : Syntax :=
mkNode `Lean.Parser.Term.explicitBinder #[mkAtom "(", mkNullNode #[n], mkNullNode #[mkAtom ":", type], mkNullNode, mkAtom ")"]

@[builtinTermElab arrow] def elabArrow : TermElab :=
fun stx expectedType? => do
  a ← mkFreshAnonymousName;
  let id     := mkIdentFrom stx.val a;
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

@[builtinTermElab paren] def elabParen : TermElab :=
fun stx expectedType? =>
  -- `(` (termParser >> parenSpecial)? `)`
  let body := stx.getArg 1;
  if body.isNone then
    pure $ mkConst `Unit.unit
  else
    let term := body.getArg 0;
    -- TODO: handle parenSpecial
    elabTerm term expectedType?

def mkTermId (ref : Syntax) (n : Name) : Syntax :=
let id := mkIdentFrom ref n;
mkNode `Lean.Parser.Term.id #[id, mkNullNode]

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

structure NamedArg :=
(name : Name)
(val  : Syntax)
(stx  : Syntax)

instance NamedArg.hasToString : HasToString NamedArg :=
⟨fun s => "(" ++ toString s.name ++ " := " ++ toString s.val ++ ")"⟩

instance NamedArg.inhabited : Inhabited NamedArg := ⟨{ name := arbitrary _, val := arbitrary _, stx := arbitrary _ }⟩

def addNamedArg (namedArgs : Array NamedArg) (namedArg : NamedArg) (ref : Syntax) : TermElabM (Array NamedArg) := do
when (namedArgs.any $ fun namedArg' => namedArg.name == namedArg'.name) $
  throwError ref ("argument '" ++ toString namedArg.name ++ "' was already set");
pure $ namedArgs.push namedArg

private def resolveLocalNameAux (lctx : LocalContext) : Name → List String → Option (Expr × List String)
| n@(Name.str pre s _), projs =>
  match lctx.findFromUserName n with
  | some decl => some (decl.toExpr, projs)
  | none      => resolveLocalNameAux pre (s::projs)
| _, _ => none

private def resolveLocalName (n : Name) : TermElabM (Option (Expr × List String)) := do
lctx ← getLCtx;
pure $ resolveLocalNameAux lctx n []

private def mkFreshLevelMVars (ref : Syntax) (num : Nat) : TermElabM (List Level) :=
num.foldM (fun _ us => do u ← mkFreshLevelMVar ref; pure $ u::us) []

private def mkConsts (ref : Syntax) (candidates : List (Name × List String)) (explicitLevels : List Level) : TermElabM (List (Expr × List String)) := do
env ← getEnv;
candidates.foldlM
  (fun result ⟨constName, projs⟩ =>
    match env.find constName with
    | none       => unreachable!
    | some cinfo =>
      if explicitLevels.length > cinfo.lparams.length then
        -- Remark: we discard candidate because of the number of explicit universe levels provided.
        pure result
      else do
        let numMissingLevels := cinfo.lparams.length - explicitLevels.length;
        us ← mkFreshLevelMVars ref numMissingLevels;
        pure $ (mkConst constName (explicitLevels ++ us), projs) :: result)
  []

def resolveName (n : Name) (preresolved : List (Name × List String)) (explicitLevels : List Level) (ref : Syntax) : TermElabM (List (Expr × List String)) := do
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
    env       ← getEnv;
    ns        ← getNamespace;
    openDecls ← getOpenDecls;
    process (resolveGlobalName env ns openDecls n)
  else
    process preresolved

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

/-- Consume parameters of the form `(x : A := val)` and `(x : A . tactic)` -/
def consumeDefaultParams (ref : Syntax) : Expr → Expr → TermElabM Expr
| eType, e =>
  -- TODO
  pure e

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

private partial def elabAppArgsAux (ref : Syntax) (args : Array Syntax) (expectedType? : Option Expr) (explicit : Bool)
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
      let arg       := namedArgs.get! idx;
      let namedArgs := namedArgs.eraseIdx idx;
      a ← elabTerm arg.val d;
      elabAppArgsAux argIdx namedArgs instMVars (b.instantiate1 a) (mkApp e a)
    | none =>
      let processExplictArg : Unit → TermElabM Expr := fun _ => do {
        if h : argIdx < args.size then do
          a ← elabTerm (args.get ⟨argIdx, h⟩) d;
          elabAppArgsAux (argIdx + 1) namedArgs instMVars (b.instantiate1 a) (mkApp e a)
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
          a ← mkFreshExprMVar ref d true;
          let mvarId := a.mvarId!;
          registerSyntheticMVar mvarId ref SyntheticMVarKind.typeClass;
          elabAppArgsAux argIdx namedArgs (instMVars.push mvarId) (b.instantiate1 a) (mkApp e a)
        | _ =>
          processExplictArg ()
  | _ =>
    if namedArgs.isEmpty && argIdx == args.size then
      finalize ()
    else
      -- TODO: try `HasCoeToFun`
      throwError ref "too many arguments"

private def elabAppArgs (ref : Syntax) (f : Expr) (namedArgs : Array NamedArg) (args : Array Syntax)
    (expectedType? : Option Expr) (explicit : Bool) : TermElabM Expr := do
fType ← inferType ref f;
let argIdx    := 0;
let instMVars := #[];
elabAppArgsAux ref args expectedType? explicit argIdx namedArgs instMVars fType f

private def elabAppProjsAux (ref : Syntax) (namedArgs : Array NamedArg) (args : Array Syntax) (expectedType? : Option Expr) (explicit : Bool)
    : Expr → List Projection → TermElabM Expr
| f, []          => elabAppArgs ref f namedArgs args expectedType? explicit
| f, proj::projs => do
  fType ← inferType ref f;
  -- TODO
  elabAppArgs ref f namedArgs args expectedType? explicit

private def elabAppProjs (ref : Syntax) (f : Expr) (projs : List Projection) (namedArgs : Array NamedArg) (args : Array Syntax)
    (expectedType? : Option Expr) (explicit : Bool) : TermElabM Expr := do
when (!projs.isEmpty && explicit) $ throwError ref "invalid use of projection notation with `@` modifier";
elabAppProjsAux ref namedArgs args expectedType? explicit f projs

private partial def elabAppFn (ref : Syntax) : Syntax → List Projection → Array NamedArg → Array Syntax → Option Expr → Bool → Array TermElabResult → TermElabM (Array TermElabResult)
| f, projs, namedArgs, args, expectedType?, explicit, acc =>
  let k := f.getKind;
  if k == `Lean.Parser.Term.explicit then
    -- `f` is of the form `@ id`
    elabAppFn (f.getArg 1) projs namedArgs args expectedType? true acc
  else if k == choiceKind then
    f.getArgs.foldlM (fun acc f => elabAppFn f projs namedArgs args expectedType? explicit acc) acc
  else if k == `Lean.Parser.Term.proj then
    -- term `.` (fieldIdx <|> ident)
    let field := f.getArg 2;
    match field.isFieldIdx?, field with
    | some idx, _                      => elabAppFn (f.getArg 0) (Projection.num idx :: projs) namedArgs args expectedType? true acc
    | _,        Syntax.ident _ val _ _ => elabAppFn (f.getArg 0) (Projection.str val.toString :: projs) namedArgs args expectedType? true acc
    | _,        _                      => throwError field "unexpected kind of field access"
  else if k == `Lean.Parser.Term.id then
    -- ident (explicitUniv | namedPattern)?
    match f.getArg 0 with
    | Syntax.ident _ _ n preresolved => do
      us     ← elabExplicitUniv (f.getArg 1); -- `namedPattern` should already have been expanded
      fprojs ← resolveName n preresolved us f;
      fprojs.foldlM
        (fun acc ⟨f, projs'⟩ => do
          let projs' := projs'.map Projection.str;
          s ← observing $ elabAppProjs ref f (projs' ++ projs) namedArgs args expectedType? explicit;
          pure $ acc.push s)
        acc
    | _ => unreachable!
  else do
    f ← withoutPostponing $ elabTerm f none;
    s ← observing $ elabAppProjs ref f projs namedArgs args expectedType? explicit;
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

private def elabAppAux (ref : Syntax) (f : Syntax) (namedArgs : Array NamedArg) (args : Array Syntax) (expectedType? : Option Expr) : TermElabM Expr := do
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

private def expandApp (stx : Syntax) : TermElabM (Syntax × Array NamedArg × Array Syntax) := do
let (f, args) := expandAppAux stx #[];
(namedArgs, args) ← args.foldlM
  (fun (acc : Array NamedArg × Array Syntax) arg =>
    let (namedArgs, args) := acc;
    arg.ifNodeKind `Lean.Parser.Term.namedArgument
      (fun argNode => do
        -- `(` ident `:=` term `)`
        namedArgs ← addNamedArg acc.1 { name := argNode.getIdAt 1, val := argNode.getArg 3, stx := arg } arg;
        pure (namedArgs, args))
      (fun _ =>
        pure (namedArgs, args.push arg)))
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

end Term

@[init] private def regTraceClasses : IO Unit := do
registerTraceClass `Elab.app;
pure ()

export Term (TermElabM)

end Elab
end Lean
