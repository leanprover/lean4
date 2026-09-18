/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Thrane Christiansen
-/
module
prelude
public import Lean.Elab.Term.TermElabM
public import Lean.Elab.Command.Scope
public import Lean.DocString.Markdown
public import Lean.DocString.View
import Lean.DocString.Syntax
import Lean.DocString.Parser
import Lean.BuiltinDocAttr
import Init.Omega

set_option linter.missingDocs true

namespace Lean.Doc

open Lean Elab Term
open _root_.Std
open scoped Lean.Doc.Syntax


public section

private structure ElabLink where
  name : VersoRefName
deriving TypeName

private def delayLink (name : VersoRefName) : ElabInline :=
  .custom (.mk (ElabLink.mk name))

private structure ElabImage where
  alt : String
  name : VersoRefName
deriving TypeName

private def delayImage (alt : String) (name : VersoRefName) : ElabInline :=
  .custom (.mk (ElabImage.mk alt name))

private structure ElabFootnote where
  name : VersoRefName
deriving TypeName

private def delayFootnote (name : VersoRefName) : ElabInline :=
  .custom (.mk (ElabFootnote.mk name))

private structure Ref (α) where
  content : α
  location : Syntax
  seen := false

/-- The internal state used by docstring elaboration -/
structure InternalState where
  private footnotes : HashMap String (Ref (Inline ElabInline)) := {}
  private urls : HashMap String (Ref String) := {}
  /-- Deferred checks accumulated while elaborating the current docstring, in source order. -/
  private deferred : Array DeferredCheck := #[]

/--
The state used by `DocM`.
-/
structure State where
  /--
  The command elaboration scope stack.

  These scopes are used when running commands inside of documentation. To keep examples
  self-contained, these scopes are initialized for each doc comment as if it were the beginning
  of a Lean file.
  -/
  scopes : List Elab.Command.Scope
  /--
  The set of open declarations presently in force.

  The `MonadLift TermElabM DocM` instance runs the lifted action in a context where these open
  declarations are used, so elaboration commands that mutate this state cause it to take effect in
  subsequent commands.
  -/
  openDecls : List OpenDecl
  /--
  The local context.

  The `MonadLift TermElabM DocM` instance runs the lifted action in this context, so elaboration
  commands that mutate this state cause it to take effect in subsequent commands.
  -/
  lctx : LocalContext
  /--
  The local instances.

  The `MonadLift TermElabM DocM` instance runs the lifted action with these instances, so elaboration
  commands that mutate this state cause it to take effect in subsequent commands.
  -/
  localInstances : LocalInstances
  /--
  The options.

  The `MonadLift TermElabM DocM` instance runs the lifted action with these options, so elaboration
  commands that mutate this state cause it to take effect in subsequent commands.
  -/
  options : Options

/--
Determines whether docstring suggestions are to be provided as part of editing the string or in a
later report.
-/
inductive SuggestionMode where
  /--
  The user is currently editing the doc comment and can react to suggestions as code actions.
  -/
  | interactive
  /--
  The user is not editing the doc comment, and should receive suggestions as summaries.
  -/
  | batch
deriving BEq, Repr

/-- Context used as a reader in `DocM`. -/
structure Context where
  /-- Whether suggestions should be provided interactively. -/
  suggestionMode : SuggestionMode

/--
The monad in which documentation is elaborated.
-/
abbrev DocM := ReaderT Context (StateRefT InternalState (StateRefT Lean.Doc.State TermElabM))

private def DocM.mk (act : Context → IO.Ref InternalState → IO.Ref State → TermElabM α) : DocM α := act

instance : MonadStateOf InternalState DocM :=
  inferInstanceAs <| MonadStateOf InternalState (ReaderT Context (StateRefT InternalState (StateRefT Lean.Doc.State TermElabM)))

instance : MonadStateOf State DocM :=
  inferInstanceAs <| MonadStateOf State (ReaderT Context (StateRefT InternalState (StateRefT Lean.Doc.State TermElabM)))


instance : MonadLift TermElabM DocM where
  monadLift act := private DocM.mk fun _ _ st' => do
    let {openDecls, lctx, options, localInstances, ..} := (← st'.get)
    let v ←
      withTheReader Core.Context (fun ρ => { ρ with openDecls, options }) <|
      withTheReader Meta.Context (fun ρ => { ρ with lctx, localInstances }) <|
      act
    return v

/--
Records a deferred check. Deferred checks represent a docstring task that can't be carried out at
the elaboration site, such as resolving a forward reference. Recorded checks include the current
namespace, open namespaces, and options, but not the local context.

The origin site `ref` is used to record the origin of the deferred check. Returns the check's index
within the current docstring, which the docstring's AST stores to refer back to it.

The saved deferred check is not associated with the docstring or module doc until it is actually
added to the environment. After this call, the internal state stores `Name.anonymous`.
-/
def addDeferredCheck (check : Dynamic) (imports : Array Name) (ref : Syntax) : DocM Nat := do
  let fileMap ← getFileMap
  let sourceString :=
    match ref.getRange? with
    | some ⟨s, e⟩ => String.Pos.Raw.extract fileMap.source s e
    | none => ""
  let index := (← getThe InternalState).deferred.size
  let entry : DeferredCheck := {
    site := .decl .anonymous
    index
    sourceString
    imports
    currNamespace := ← getCurrNamespace
    openDecls := ← getOpenDecls
    options := ← getOptions
    check
  }
  modifyThe InternalState fun s => { s with deferred := s.deferred.push entry }
  return index

private structure ModuleDocstringState extends Lean.Doc.State where
  scopedExts : Array (ScopedEnvExtension EnvExtensionEntry EnvExtensionEntry EnvExtensionState)

private builtin_initialize modDocstringStateExt : EnvExtension (Option ModuleDocstringState) ←
  registerEnvExtension (pure none)

private def getModState
    [Monad m] [MonadEnv m] [MonadLiftT IO m] [MonadLiftT MetaM m] [MonadLCtx m]
    [MonadResolveName m] [MonadOptions m] : m ModuleDocstringState := do
  if let some st := modDocstringStateExt.getState (← getEnv) then
    return st
  else
    let scopes := [{header := "", isPublic := true}]
    let openDecls ← getOpenDecls
    let lctx ← getLCtx
    let localInstances ← Meta.getLocalInstances
    let options ← getOptions
    let scopedExts := #[]
    let st : ModuleDocstringState :=
      { scopes, openDecls, lctx, localInstances, options, scopedExts }
    modifyEnv fun env =>
      modDocstringStateExt.setState env st
    return st

private def setModState [Monad m] [MonadEnv m] (state : ModuleDocstringState) : m Unit := do
  modifyEnv fun env =>
    modDocstringStateExt.setState env state

/--
Reports errors registered via `Term.registerMVarErrorInfo` for any metavariable still appearing in
the types or values of fresh local declarations introduced during docstring elaboration. This
catches unresolved holes from `{given}` and `{givenInstance}` before the term state is rolled back.
-/
private def checkUnsolvedDocMVars (initialLctx : LocalContext) (docState : State) :
    TermElabM Unit := do
  let mut pending : Array MVarId := #[]
  for decl in docState.lctx do
    unless initialLctx.containsFVar (.fvar decl.fvarId) do
      pending := pending ++ (← Meta.getMVars (← instantiateMVars decl.type))
      if let some v := decl.value? then
        pending := pending ++ (← Meta.getMVars (← instantiateMVars v))
  unless pending.isEmpty do
    discard <| Term.logUnassignedUsingErrorInfos pending

/--
Runs a `TermElabM` action, saving and restoring the term elaboration state so that metavariables
and other state changes do not leak. Messages produced by the action are preserved.
-/
private def withSaveRestoreTermState (act : TermElabM α) : TermElabM α := do
  let termSt ← Term.saveState
  Core.resetMessageLog
  try
    act
  finally
    let msgs ← Core.getMessageLog
    termSt.restore
    Core.setMessageLog ((← Core.getMessageLog) ++ msgs)

/--
Runs a documentation elaborator in the module docstring context.
-/
def DocM.execForModule (act : DocM α) (suggestionMode : SuggestionMode := .interactive) :
    TermElabM (α × Array DeferredCheck) := withoutModifyingEnv do
  let sc ← scopedEnvExtensionsRef.get
  let st ← getModState
  withSaveRestoreTermState do
    try
      scopedEnvExtensionsRef.set st.scopedExts
      let ((v, internalSt), docState) ←
        act.run { suggestionMode } |>.run {} |>.run st.toState
      checkUnsolvedDocMVars st.toState.lctx docState
      pure (v, internalSt.deferred)
    finally
      scopedEnvExtensionsRef.set sc

open Lean.Parser.Term in
/--
Runs a documentation elaborator in a declaration's context, discarding changes made to the
environment.
-/
def DocM.exec (declName : Name) (binders : Syntax) (act : DocM α)
    (suggestionMode : SuggestionMode := .interactive) :
    TermElabM (α × Array DeferredCheck) := withoutModifyingEnv do
  let some ci := (← getEnv).constants.find? declName
    | throwError "Unknown constant {declName} when building docstring"
  withSaveRestoreTermState do
    let (lctx, localInstances) ← buildContext ci.type binders
    let sc ← scopedEnvExtensionsRef.get
    try
      let openDecls ← getOpenDecls
      let options ← getOptions
      let scopes := [{header := "", isPublic := true}]
      let ((v, internalSt), docState) ← withTheReader Meta.Context (fun ρ => { ρ with localInstances }) <|
        act.run { suggestionMode } |>.run {} |>.run { scopes, openDecls, lctx, localInstances, options }
      checkUnsolvedDocMVars lctx docState
      pure (v, internalSt.deferred)
    finally
      scopedEnvExtensionsRef.set sc
where
  buildContext (type : Expr) (binders : Syntax) : TermElabM (LocalContext × LocalInstances) := do
    -- Create a local context with all binders. The type will be updated as we introduce parameters.
    let mut type := type

    -- We start with a local context that's reset to only include section variables
    let mut localInstances ← Meta.getLocalInstances
    let mut lctx ← getLCtx
    let sectionFVars := (← read).sectionFVars.valuesArray.filterMap fun
      | .fvar fv => some fv
      | _ => none
    repeat
      if lctx.size = 0 then break
      if let some decl := lctx.lastDecl then
        if sectionFVars.any (· == decl.fvarId) then break
        else
          lctx := lctx.pop
          localInstances := localInstances.filter (·.fvar != .fvar decl.fvarId)
      else break

    let names ← binders.getArgs.flatMapM binderNames
    let mut i := 0
    let mut x := none
    repeat -- Consume parameters until we find one that matches or run out
      if x.isNone then
        x := names[i]?
        i := i + 1
      type ← Meta.withLCtx lctx localInstances <| Meta.whnf type
      match type with
      | .forallE y ty body bi =>
        let fv ← mkFreshFVarId
        if let some c := ← Meta.withLCtx lctx localInstances (Meta.isClass? ty) then
          localInstances := localInstances.push {className := c, fvar := .fvar fv}

        if let some (some x') := x then
          if x'.getKind == ``hole then
            -- A `_` parameter has no name, so it matches no binder. Drop it from the cursor
            -- and align the remaining parameters by name; each lifted binder, including
            -- captured variables, is introduced under its own name below.
            x := none
          else if x'.getId == y then
            lctx := lctx.mkLocalDecl fv y ty
            Meta.withLCtx lctx localInstances <|
              addTermInfo' x' (.fvar fv) (lctx? := some lctx) (expectedType? := ty)
            type := body.instantiate1 (.fvar fv)
            x := none
            continue
        else if let some none := x then
          if bi == .instImplicit then
            lctx := lctx.mkLocalDecl fv y ty
            type := body.instantiate1 (.fvar fv)
            x := none
            continue

        lctx := lctx.mkLocalDecl fv y ty
        type := body.instantiate1 (.fvar fv)
      | .mdata _ t => type := t
      | _ => break
    return (lctx, localInstances)

  binderNames (binderStx : Syntax) : TermElabM (Array (Option Syntax)) :=
    match binderStx.getKind with
    | ``explicitBinder | ``implicitBinder | ``strictImplicitBinder =>
      getNames binderStx[1]
    | ``instBinder =>
      let x := binderStx[1][0]
      if x.isMissing then pure #[none] else pure #[some x]
    | k =>
      -- A parameter bound by an unbracketed identifier or `_`, as in `def f x` or `where go _`.
      if k == identKind || k == ``hole then pure #[some binderStx]
      else throwErrorAt binderStx "Couldn't interpret binder {binderStx}"
  getNames (ids : Syntax) : TermElabM (Array (Option Syntax)) :=
    ids.getArgs.mapM fun x =>
      if x.getKind == identKind || x.getKind == ``hole then
        pure (some x)
      else throwErrorAt x "identifier or `_` expected"


set_option linter.unusedVariables false in
/--
Gadget that indicates that a function's parameter should be treated as a Boolean flag when used in
a docstring extension.
-/
abbrev flag (default : Bool) : Type := Bool

/--
Gadget that indicates that a function's parameter should be treated as a repeated (and thus
optional) named argument when used in a docstring extension.
-/
abbrev many (α : Type u) : Type u := Array α


/-- An argument provided to a docstring extension -/
inductive DocArg where
  /-- An identifier -/
  | ident (val : Ident)
  /-- A number -/
  | num (val : NumLit)
  /-- A string -/
  | str (val : StrLit)

instance : ToMessageData DocArg where
  toMessageData
    | .ident x => toMessageData x
    | .num n => toMessageData n
    | .str s => toMessageData s

/--
Returns the syntax from which a documentation argument was drawn, typically used to report errors.
-/
def DocArg.syntax : DocArg → Syntax
  | .ident x => x
  | .num x => x
  | .str x => x

/--
Converts the syntax of a documentation argument into a suitable value.
-/
def DocArg.ofSyntax (stx : TSyntax ``Parser.argVal) : TermElabM DocArg :=
  match ArgValView.of stx with
  | some (.name x) => pure <| .ident x
  | some (.num n _) => pure <| .num n
  | some (.str s _) => pure <| .str s
  | none => throwErrorAt stx "Failed to parse argument value"

/--
A value paired with the syntax it is derived from.

This can be used to provide hints and code actions.
-/
structure WithSyntax (α : Type u) where
  /-- The parsed value. -/
  val : α
  /-- The syntax that the value was derived from. -/
  stx : Syntax

/--
A canonical way to convert a documentation extension's argument into a Lean value of type `α`.
-/
class FromDocArg α where
  /--
  Converts a documentation extension's argument into a Lean value.
  -/
  fromDocArg : DocArg → TermElabM α

instance [FromDocArg α] : FromDocArg (Option α) where
  fromDocArg v := private some <$> FromDocArg.fromDocArg v

instance [FromDocArg α] : FromDocArg (WithSyntax α) where
  fromDocArg v := private (WithSyntax.mk · v.syntax) <$> FromDocArg.fromDocArg v

instance : FromDocArg Ident where
  fromDocArg v := private
    match v with
    | .ident x => pure x
    | other => throwErrorAt other.syntax "Expected a string"

instance : FromDocArg String where
  fromDocArg v := private
    match v with
    | .str s => pure s.getString
    | other => throwErrorAt other.syntax "Expected a string"

instance : FromDocArg StrLit where
  fromDocArg v := private
    match v with
    | .str s => pure s
    | other => throwErrorAt other.syntax "Expected a string"

instance : FromDocArg Nat where
  fromDocArg v := private
    match v with
    | .num x => pure x.getNat
    | other => throwErrorAt other.syntax "Expected a number"

instance : FromDocArg NumLit where
  fromDocArg v := private
    match v with
    | .num x => pure x
    | other => throwErrorAt other.syntax "Expected a number"

instance : FromDocArg DataValue where
  fromDocArg v := private
    match v with
    | .num x => pure <| .ofNat x.getNat
    | .ident x => do
      let y ← realizeGlobalConstNoOverloadWithInfo x
      if y == ``true then pure <| .ofBool true
      else if y == ``false then pure <| .ofBool false
      else
        let bools ← #[``true, ``false] |>.mapM unresolveNameGlobalAvoidingLocals
        let h ← MessageData.hint m!"Use a Boolean:" (bools.map fun x => s!"{x}") (ref? := some x)
        throwErrorAt x m!"Expected a string, number, or Boolean.{h}"
    | .str s => pure <| .ofString s.getString

instance : FromDocArg Bool where
  fromDocArg v := private
    match v with
    | .ident x => do
      let x' ← realizeGlobalConstNoOverloadWithInfo x
      if x' == ``true then return true
      else if x' == ``false then return false
      else throwErrorAt x m!"Expected {.ofConstName ``true} or {.ofConstName ``false} but got {.ofConstName x'}"
    | other => throwErrorAt other.syntax "Expected a Boolean"

open MessageSeverity in
private def severityHint (ref : Syntax) : TermElabM MessageData := do
    let suggestions ← #[``information, ``warning, ``error].mapM unresolveNameGlobalAvoidingLocals
    let suggestions:= suggestions.map ({suggestion := ·.toString})
    MessageData.hint m!"Use a message severity:" suggestions (ref? := ref)

open MessageSeverity in
instance : FromDocArg MessageSeverity where
  fromDocArg v := private
    match v with
    | .ident x => do
      let x' ←
        try realizeGlobalConstNoOverloadWithInfo x
        catch
          | e => throwErrorAt x m!"{e.toMessageData}{← severityHint x}"
      match x' with
      | ``error => return error
      | ``warning => return warning
      | ``information => return information
      | _ =>
        let expected := [``information, ``warning, ``error].map (MessageData.ofConstName)
        throwErrorAt x m!"Expected {.orList expected} but got {.ofConstName x'}{← severityHint x}"
    | other => do
      throwErrorAt other.syntax "Expected a message severity{← severityHint other.syntax}"

/--
Retrieves the next positional argument from the arguments to a documentation extension. Throws
an error if no positional arguments remain.
-/
protected def getPositional [FromDocArg α] (name : Name) :
    StateT (Array (TSyntax `doc_arg)) DocM α := do
  let args ← get
  for h : i in [0:args.size] do
    if let some (.anon _ v) := ArgView.of args[i] then
      set (σ := Array (TSyntax `doc_arg)) (args[:i] ++ args[i+1:])
      let v ← DocArg.ofSyntax v
      return (← FromDocArg.fromDocArg v)
  throwError "Missing positional argument `{name}`"

private def asNamed (stx : TSyntax `doc_arg) :
    Option (Ident × TSyntax ``Parser.argVal) :=
  match ArgView.of stx with
  | some (.named _ _ x _ v) => some (x, v)
  | _ => none

/--
Retrieves a named argument from the arguments to a documentation extension. Returns `default` if no
such named argument was provided.
-/
protected def getNamed [FromDocArg α] (name : Name) (default : α) :
    StateT (Array (TSyntax `doc_arg)) DocM α := do
  let name := name.eraseMacroScopes
  let args ← get
  for h : i in [0:args.size] do
    if let some (x, v) := asNamed args[i] then
      if x.getId.eraseMacroScopes == name then
        set (σ := Array (TSyntax `doc_arg)) (args[:i] ++ args[i+1:])
        let v ← DocArg.ofSyntax v
        return (← FromDocArg.fromDocArg v)
  return default

/--
Retrieves a repeated named argument from the arguments to a documentation extension.
-/
protected def getMany [FromDocArg α] (name : Name) :
    StateT (Array (TSyntax `doc_arg)) DocM (Array α) := do
  let name := name.eraseMacroScopes
  let args ← get
  let mut thisArg := #[]
  let mut others := #[]
  for arg in args do
    if let some (x, v) := asNamed arg then
      if x.getId.eraseMacroScopes == name then
        let v ← DocArg.ofSyntax v
        thisArg := thisArg.push v
        continue
    others := others.push arg
  set others
  thisArg.mapM (FromDocArg.fromDocArg ·)

/--
Retrieves a flag from the arguments to a documentation extension. Returns `default` if the flag is
not explicit set.
-/
protected def getFlag (name : Name) (default : Bool) : StateT (Array (TSyntax `doc_arg)) DocM Bool := do
  let name := name.eraseMacroScopes
  let args ← get
  for h : i in [0:args.size] do
    if let some (x, v) := asFlag args[i] then
      if x.getId.eraseMacroScopes == name then
        set (σ := Array (TSyntax `doc_arg)) (args[:i] ++ args[i+1:])
        return v
  return default
where
  asFlag (stx : TSyntax `doc_arg) : Option (Ident × Bool) :=
    match ArgView.of stx with
    | some (.flag _ _ x isOn) => some (x, isOn)
    | _ => none

/--
Asserts that there are no further arguments to a documentation language extension.
-/
protected def done : StateT (Array (TSyntax `doc_arg)) DocM Unit := do
  for arg in (← get) do
    match ArgView.of arg with
    | some (.flag _ _ x _) =>
      logErrorAt arg m!"Unexpected flag `{x.getId}`"
    | some (.named _ _ x _ _) =>
      logErrorAt arg m!"Unexpected named argument `{x.getId}`"
    | some (.anon ..) =>
      logErrorAt arg m!"Unexpected positional argument"
    | none =>
      logErrorAt arg m!"Unexpected argument"
  return

private inductive ArgSpec where
  | positional (name : Name) (type : Expr)
  | named (name : Name) (type : Expr) (default : Expr)
  | many (name : Name) (type : Expr)
  | flag (name : Name) (default : Bool)
  | view (name : Name) (type : Expr) (get : Name)
deriving Repr

/-- The singleton list of syntax node kinds that contains only `kind`. -/
private def oneKind (kind : Name) : Expr :=
  mkApp3 (.const ``List.cons [0]) (.const ``SyntaxNodeKind []) (toExpr kind)
    (.app (.const ``List.nil [0]) (.const ``SyntaxNodeKind []))

/-- The type of syntax that has only the kind `kind`. -/
private def tSyntaxOfCat (kind : Name) : Expr :=
  .app (.const ``TSyntax []) (oneKind kind)

/-- The type of an array of syntax that has only the kind `kind`. -/
private def tSyntaxArrayOfCat (kind : Name) : Expr :=
  .app (.const ``TSyntaxArray []) (oneKind kind)

section Migration
/-
The function in this section is a temporary bootstrapping adaptation. A wrapper receives inline and
block content in the `Lean.Doc.Syntax` encoding and literal content as a string literal, while the
declaration it wraps may have a parameter of the parser's kinds or of a content token. After a
stage0 update a wrapper can receive those directly, and this section can be deleted along with
`alsoAccept`.
-/

open Meta in
/--
Converts `e` from type `source` to type `target`.
-/
private def convertContent (e source target : Expr) : MetaM Expr := do
  if ← isDefEq source target then return e
  -- Inline and block content may be written in either encoding.
  let encodings : Array (Name × Name × Name) := #[
    (`inline, ``Parser.inline, ``Lean.Doc.migrateInlines),
    (`block, ``Parser.block, ``Lean.Doc.migrateBlocks)]
  for (cat, parserCat, conversion) in encodings do
    if (← isDefEq source (tSyntaxArrayOfCat cat)) &&
        (← isDefEq target (tSyntaxArrayOfCat parserCat)) then
      return mkApp (.const conversion []) e
  -- A wrapper receives literal content as a string literal.
  let conversions : Array (Name × Name × Name) := #[
    (``StrLit, ``Lean.Doc.VersoCode, ``Lean.Doc.versoCodeOfStrLit),
    (``StrLit, ``Lean.Doc.VersoCodeBlock, ``Lean.Doc.versoCodeBlockOfStrLit)]
  for (from', to, conversion) in conversions do
    if (← isDefEq source (.const from' [])) && (← isDefEq target (.const to [])) then
      return mkApp (.const conversion []) e
  throwError "Cannot convert `{.ofExpr source}` to `{.ofExpr target}`"

end Migration

open Meta in
/--
The type of the content parameter of `declName`, which is its last parameter. Fails unless the type
is one of `accepted`.
-/
private def contentParamType (declName : Name) (accepted : Array Expr) : MetaM Expr := do
  let some c := (← getEnv).constants.find? declName
    | throwError m!"`{MessageData.ofConstName declName}` not found"
  forallTelescope c.type fun args _ => do
    let some final := args[args.size - 1]?
      | throwError "Expected a content parameter on `{.ofConstName declName}`"
    let ty := (← final.fvarId!.getDecl).type
    unless ← accepted.anyM (fun t => isDefEq ty t) do
      let names := ", ".intercalate (accepted.toList.map (s!"`{·}`"))
      throwError "Expected type of last parameter to `{.ofConstName declName}` to be one of \
        {names} but got `{.ofExpr ty}`"
    pure ty

/-- The view of each kind of document element, with a description of the element. -/
private def elementViews : Array (Name × String) := #[
  (``RoleView, "role"),
  (``DirectiveView, "directive"),
  (``CodeBlockView, "code block"),
  (``CommandView, "block-level command")]

open Meta in
/--
Generates the wrapper that presents `declName` to the document elaborator. The wrapper reads the
declaration's named arguments from a document's argument syntax.

The wrapper receives the content as `argType` and converts it to the type of `declName`'s last
parameter, which may be `argType` or any type in `alsoAccept`. The compiler that builds `declName`
provides the attribute, so that compiler decides which types are allowed.

`view?` gives the type of the view of the element being elaborated, together with the function that
reads it. A parameter of that type is filled from the reference rather than from the arguments.
-/
private def genWrapper (declName : Name) (argType : Option Expr) (retType : Expr)
    (alsoAccept : Array Expr := #[])
    (view? : Option (Expr × Name) := none) : TermElabM Name := do
  if let some c := (← getEnv).constants.find? declName then
    let argSpec ← forallTelescope c.type fun args ret => do
      let mut argSpec : Array ArgSpec := #[]

      for arg in (if argType.isSome then (args[:args.size-1] : Array _) else args) do
        let localDecl ← arg.fvarId!.getDecl
        let name := localDecl.userName
        let argType := localDecl.type
        let asView? ←
          match view? with
          | some (viewTy, get) =>
            if ← isDefEq argType viewTy then pure (some (viewTy, get)) else pure none
          | none => pure none
        -- The parameters are the arguments, then the view, then the content.
        if let some (.view prev ..) := argSpec.find? (· matches .view ..) then
          if asView?.isSome then
            throwError "`{.ofConstName declName}` takes the view of the element twice, as \
              `{prev}` and as `{name}`, but there can be at most one view."
          else
            throwError "`{.ofConstName declName}` takes the argument `{name}` after the view \
              `{prev}`. Arguments must precede a view."
        -- A parameter whose type is another element's view is a mistake worth naming, because it
        -- would otherwise be read as an argument and fail to find a `FromDocArg` instance.
        let mut otherView? : Option (Name × String) := none
        if asView?.isNone then
          for (viewName, kind) in elementViews do
            if ← isDefEq argType (.const viewName []) then
              otherView? := some (viewName, kind)
        if let some (viewName, kind) := otherView? then
          match view? with
          | some (expected, _) =>
            throwError "`{.ofConstName declName}` takes `{name} : {.ofConstName viewName}`, which \
              is the view of a {kind}. Use `{.ofExpr expected}` instead."
          | none =>
            throwError "`{.ofConstName declName}` takes `{name} : {.ofConstName viewName}`, which \
              is the view of a {kind}. This extension has no view."
        if let some (viewTy, get) := asView? then
          argSpec := argSpec.push (.view name viewTy get)
        else if argType.isAppOfArity' ``optParam 2 then
          argSpec := argSpec.push (.named name (argType.getArg! 0) (argType.getArg! 1))
        else if argType.isAppOfArity' ``many 1 then
          argSpec := argSpec.push (.many name (argType.getArg!' 0))
        else if argType.isAppOfArity' ``flag 1 then
          let e ← whnf (argType.getArg!' 0)
          match_expr e with
          | true => argSpec := argSpec.push (.flag name true)
          | false => argSpec := argSpec.push (.flag name false)
          | _ => throwError m!"Couldn't determine default flag value from {e}"
        else
          argSpec := argSpec.push (.positional name argType)
      let expected ← mkAppM ``DocM #[retType]
      unless ← isDefEq ret expected do
        throwError "Expected return type of `{.ofConstName declName}` to be `{.ofExpr expected}` but got `{.ofExpr ret}`"

      pure argSpec
    let parser ←
      if let some argType := argType then
        -- The wrapper takes the content as `argType`, whatever the declaration's parameter is.
        let declared ← contentParamType declName (#[argType] ++ alsoAccept)
        withLocalDecl (← mkFreshBinderName) .default argType fun i => do
          let content ← convertContent i argType declared
          mkLambdaFVars #[i] (← build 0 argSpec #[] (some content))
      else build 0 argSpec #[] none
    let parserTy ← inferType parser
    let name := declName ++ `getArgs
    -- Re-use an existing wrapper instead of generating a new one with a conflicting name. This can
    -- happen when the same implementation is used for multiple roles/directives/code
    -- blocks/commands.
    if let some existing := (← getEnv).find? name then
      unless (← isDefEq existing.type parserTy) &&
          (← existing.value?.mapM (isDefEq · parser)).getD false do
        throwError "`{.ofConstName name}` is not the wrapper for `{.ofConstName declName}`"
    else
      let isMeta := isMarkedMeta (← getEnv) declName
      addAndCompile (markMeta := isMeta) <| .defnDecl {
        name
        levelParams := []
        type := parserTy
        value := parser
        hints := .regular 0
        safety := .safe
      }
      -- The wrapper shows the declaration's documentation.
      if (← findInternalDocString? (← getEnv) declName).isSome then
        addInheritedDocString name declName
    return name
  else
    throwError m!"`{MessageData.ofConstName declName}` not found"
where
  build (i : Nat) (argSpec : Array ArgSpec) (args : Array Expr) (body : Option Expr): MetaM Expr := do
    if h : i < argSpec.size then
      match argSpec[i] with
      | .positional name type =>
        let arg ← mkAppOptM ``Lean.Doc.getPositional #[type, none, toExpr name]
        let k ← withLocalDecl name .default type fun v => do
            mkLambdaFVars #[v] (← build (i + 1) argSpec (args.push v) body)
        mkAppM ``Bind.bind #[arg, k]
      | .named name type default =>
        let arg ← mkAppOptM ``Lean.Doc.getNamed #[type, none, toExpr name, default]
        let k ← withLocalDecl name .default type fun v => do
            mkLambdaFVars #[v] (← build (i + 1) argSpec (args.push v) body)
        mkAppM ``Bind.bind #[arg, k]
      | .many name type =>
        let arg ← mkAppOptM ``Lean.Doc.getMany #[type, none, toExpr name]
        let k ← withLocalDecl name .default (← mkAppM ``Array #[type]) fun v => do
            mkLambdaFVars #[v] (← build (i + 1) argSpec (args.push v) body)
        mkAppM ``Bind.bind #[arg, k]
      | .flag name default =>
        let arg ← mkAppM ``Lean.Doc.getFlag #[toExpr name, toExpr default]
        let k ← withLocalDecl name .default (.const ``Bool []) fun v => do
            mkLambdaFVars #[v] (← build (i + 1) argSpec (args.push v) body)
        mkAppM ``Bind.bind #[arg, k]
      | .view name type get =>
        let arg := .const get []
        let k ← withLocalDecl name .default type fun v => do
            mkLambdaFVars #[v] (← build (i + 1) argSpec (args.push v) body)
        mkAppM ``Bind.bind #[arg, k]
    else
      let last ← mkAppM ``Lean.Doc.done #[]
      let m ← mkAppM ``StateT #[← mkAppM ``Array #[tSyntaxOfCat `doc_arg], ← mkAppM ``DocM #[]]
      let k ← withLocalDecl (← mkFreshBinderName) .default (.const ``Unit []) fun u => do
        let args := body.map (args.push ·) |>.getD args
        mkLambdaFVars #[u] (← mkAppOptM ``liftM #[none, some m, none, none, (← mkAppM declName args)])
      mkAppM ``Bind.bind #[last, k]

open Meta in
/--
The name to register for a suggestion provider.

A provider whose content parameter is already `contentType` is registered under its own name. Any
other provider is registered as a generated adapter that converts the content.
-/
private def genSuggesterAdapter (declName : Name) (contentType suggestionType : Expr)
    (alsoAccept : Array Expr := #[]) : TermElabM Name := do
  let retType ← mkAppM ``DocM #[← mkAppM ``Array #[suggestionType]]
  let some c := (← getEnv).constants.find? declName
    | throwError m!"`{MessageData.ofConstName declName}` not found"
  forallTelescope c.type fun args ret => do
    unless args.size == 1 do
      throwError "Expected exactly one parameter to `{.ofConstName declName}`"
    unless ← isDefEq ret retType do
      throwError "Expected return type of `{.ofConstName declName}` to be `{.ofExpr retType}` \
        but got `{.ofExpr ret}`"
  let declared ← contentParamType declName (#[contentType] ++ alsoAccept)
  if ← isDefEq declared contentType then return declName
  let value ← withLocalDecl (← mkFreshBinderName) .default contentType fun content => do
    mkLambdaFVars #[content] (mkApp (.const declName []) (← convertContent content contentType declared))
  let name := declName ++ `adapt
  let adapterTy ← inferType value
  -- Re-use the adapter if it already exists
  if let some existing := (← getEnv).find? name then
    unless ← isDefEq existing.type adapterTy do
      throwError "`{.ofConstName name}` has type `{.ofExpr existing.type}`, but the adapter for \
        `{.ofConstName declName}` has type `{.ofExpr adapterTy}`"
  else
    addAndCompile (markMeta := isMarkedMeta (← getEnv) declName) <| .defnDecl {
      name
      levelParams := []
      type := adapterTy
      value
      hints := .regular 0
      safety := .safe
    }
  return name

/-- Environment extension for code suggestions -/
builtin_initialize codeSuggestionExt : SimpleScopedEnvExtension Name NameSet ←
  registerSimpleScopedEnvExtension {
    addEntry := fun xs suggester => xs.insert suggester
    initial := {}
  }

/-- Environment extension for code block suggestions -/
builtin_initialize codeBlockSuggestionExt : SimpleScopedEnvExtension Name NameSet ←
  registerSimpleScopedEnvExtension {
    addEntry := fun xs suggester => xs.insert suggester
    initial := {}
  }


/-- Environment extension for docstring roles -/
builtin_initialize docRoleExt : SimpleScopedEnvExtension (Name × Name) (NameMap (Array Name)) ←
  registerSimpleScopedEnvExtension {
    addEntry := fun xs (roleName, expander) => xs.alter roleName fun v? =>
      v?.getD #[] |>.push expander
    initial := {}
  }

/--
An expander for roles in docstrings.
-/
abbrev DocRoleExpander :=
  TSyntaxArray `inline → StateT (Array (TSyntax `doc_arg)) DocM (Inline ElabInline)

/--
An expander for commands in docstrings.
-/
abbrev DocCommandExpander :=
  StateT (Array (TSyntax `doc_arg)) DocM (Block ElabInline ElabBlock)

/--
An expander for directives in docstrings.
-/
abbrev DocDirectiveExpander :=
  TSyntaxArray `block → StateT (Array (TSyntax `doc_arg)) DocM (Block ElabInline ElabBlock)

/--
An expander for code blocks in docstrings.
-/
abbrev DocCodeBlockExpander :=
  StrLit → StateT (Array (TSyntax `doc_arg)) DocM (Block ElabInline ElabBlock)

section Migration
/-
The functions in this section are temporary bootstrapping adaptations. The elaborator receives
syntax in the parser's encoding, while `DocRoleExpander` and its siblings use the `Lean.Doc.Syntax`
categories, so the elaborator retags the syntax at each call to an expander. After a stage0 update
the expander types can use the parser's syntax kinds, and this section can be deleted.
-/

/-- Retags inline elements for an expander. -/
private def asInlineCat (inls : TSyntaxArray ``Parser.inline) :
    TSyntaxArray `inline :=
  TSyntaxArray.mk inls.raw

/-- Retags blocks for an expander. -/
private def asBlockCat (blks : TSyntaxArray ``Parser.block) :
    TSyntaxArray `block :=
  TSyntaxArray.mk blks.raw

/-- Retags arguments for an expander. -/
private def asArgCat (args : TSyntaxArray ``Parser.arg) :
    Array (TSyntax `doc_arg) :=
  TSyntaxArray.mk args.raw

end Migration

/-!
An expander may declare a parameter whose type is the view of the element it expands. The wrapper
fills such a parameter from the reference that the elaborator establishes around the call, rather
than from the element's arguments.
-/

/-- The view of the role that is being elaborated. -/
protected def getRoleView : StateT (Array (TSyntax `doc_arg)) DocM RoleView := do
  let some v := RoleView.of ⟨← getRef⟩
    | throwError "Expected a role"
  return v

/-- The view of the directive that is being elaborated. -/
protected def getDirectiveView : StateT (Array (TSyntax `doc_arg)) DocM DirectiveView := do
  let some v := DirectiveView.of ⟨← getRef⟩
    | throwError "Expected a directive"
  return v

/-- The view of the code block that is being elaborated. -/
protected def getCodeBlockView : StateT (Array (TSyntax `doc_arg)) DocM CodeBlockView := do
  let some v := CodeBlockView.of ⟨← getRef⟩
    | throwError "Expected a code block"
  return v

/-- The view of the block-level command that is being elaborated. -/
protected def getCommandView : StateT (Array (TSyntax `doc_arg)) DocM CommandView := do
  let some v := CommandView.of ⟨← getRef⟩
    | throwError "Expected a block-level command"
  return v

/--
Built-in docstring roles, for bootstrapping.
-/
builtin_initialize builtinDocRoles : IO.Ref (NameMap (Array (Name × DocRoleExpander))) ← IO.mkRef {}


/-- Environment extension for docstring roles -/
builtin_initialize docCodeBlockExt : SimpleScopedEnvExtension (Name × Name) (NameMap (Array Name)) ←
  registerSimpleScopedEnvExtension {
    addEntry := fun xs (roleName, expander) => xs.alter roleName fun v? =>
      v?.getD #[] |>.push expander
    initial := {}
  }

/--
Built-in docstring code blocks, for bootstrapping.
-/
builtin_initialize
  builtinDocCodeBlocks : IO.Ref (NameMap (Array (Name × DocCodeBlockExpander))) ← IO.mkRef {}


/-- Environment extension for docstring directives -/
builtin_initialize docDirectiveExt : SimpleScopedEnvExtension (Name × Name) (NameMap (Array Name)) ←
  registerSimpleScopedEnvExtension {
    addEntry := fun xs (roleName, expander) => xs.alter roleName fun v? =>
      v?.getD #[] |>.push expander
    initial := {}
  }

/--
Built-in docstring directives, for bootstrapping.
-/
builtin_initialize
  builtinDocDirectives : IO.Ref (NameMap (Array (Name × DocDirectiveExpander))) ← IO.mkRef {}

/-- Environment extension for docstring commands -/
builtin_initialize docCommandExt : SimpleScopedEnvExtension (Name × Name) (NameMap (Array Name)) ←
  registerSimpleScopedEnvExtension {
    addEntry := fun xs (roleName, expander) => xs.alter roleName fun v? =>
      v?.getD #[] |>.push expander
    initial := {}
  }

/--
Built-in docstring commands, for bootstrapping.
-/
builtin_initialize
  builtinDocCommands : IO.Ref (NameMap (Array (Name × DocCommandExpander))) ← IO.mkRef {}

/-- A suggestion about an applicable role -/
structure CodeSuggestion where
  /-- The name of the role to suggest. -/
  role : Name
  /-- The arguments it should receive, as a string. -/
  args : Option String := none
  /-- More information to show users -/
  moreInfo : Option String := none

builtin_initialize registerBuiltinAttribute {
  name := `doc_code_suggestions
  descr := "docstring code element suggestion provider"
  applicationTime := .afterCompilation
  add := fun decl stx kind => do
    let ((name, _), _) ←
      genSuggesterAdapter decl (.const ``StrLit []) (.const ``CodeSuggestion [])
          (alsoAccept := #[.const ``Lean.Doc.VersoCode []])
        |>.run {} {} |>.run {} {}
    codeSuggestionExt.add name
}

/--
A provider of suggestions for code elements.
-/
abbrev CodeSuggester := StrLit → DocM (Array CodeSuggestion)

/--
Built-in code suggestions, for bootstrapping
-/
builtin_initialize
  builtinCodeSuggestions : IO.Ref (Array (Name × CodeSuggester)) ← IO.mkRef #[]

/--
Adds a builtin documentation code suggestion provider.

Should be run during initialization.
-/
def addBuiltinCodeSuggestion (decl : Name) (val : CodeSuggester) : IO Unit :=
  builtinCodeSuggestions.modify (·.push (decl, val))

builtin_initialize registerBuiltinAttribute {
  name := `builtin_doc_code_suggestions
  descr := "docstring code element suggestion provider"
  applicationTime := .afterCompilation
  add := fun decl stx kind => do
    let ((name, _), _) ←
      genSuggesterAdapter decl (.const ``StrLit []) (.const ``CodeSuggestion [])
          (alsoAccept := #[.const ``Lean.Doc.VersoCode []])
        |>.run {} {} |>.run {} {}
    declareBuiltin decl <|
      mkApp2 (.const ``addBuiltinCodeSuggestion []) (toExpr decl) (.const name [])
}

/--
The view type accepted by role expanders along with the function that reads it from the parameters.
-/
private def roleViewSpec : Option (Expr × Name) :=
  some (.const ``RoleView [], ``Lean.Doc.getRoleView)

/--
The view type accepted by directive expanders along with the function that reads it from the
parameters.
-/
private def directiveViewSpec : Option (Expr × Name) :=
  some (.const ``DirectiveView [], ``Lean.Doc.getDirectiveView)

/--
The view type accepted by code block expanders along with the function that reads it from the
parameters.
-/
private def codeBlockViewSpec : Option (Expr × Name) :=
  some (.const ``CodeBlockView [], ``Lean.Doc.getCodeBlockView)

/--
The view type accepted by command expanders along with the function that reads it from the
parameters.
-/
private def commandViewSpec : Option (Expr × Name) :=
  some (.const ``CommandView [], ``Lean.Doc.getCommandView)

/--
In module mode, docstring extensions are invoked at elaboration time, so the underlying definition
must be marked `meta`.
-/
private def checkDocExtMeta (decl : Name) (kind : String) : CoreM Unit := do
  if (← getEnv).header.isModule && !isMarkedMeta (← getEnv) decl then
    throwError m!"`{.ofConstName decl}` must be marked `meta` to be used as a docstring {kind}"

builtin_initialize registerBuiltinAttribute {
  name := `doc_role
  descr := "docstring role expander"
  applicationTime := .afterCompilation
  add := fun decl stx kind => do
    checkDocExtMeta decl "role"
    let roleName ←
      if let `(attr|doc_role $x) := stx then
        realizeGlobalConstNoOverloadWithInfo x
      else
        pure decl
    let argTy := tSyntaxArrayOfCat `inline
    let ret := .app (.const ``Inline [0]) (.const ``ElabInline [])
    let ((wrapper, _), _) ←
      genWrapper decl (some argTy) ret (alsoAccept := #[tSyntaxArrayOfCat ``Parser.inline])
          (view? := roleViewSpec)
        |>.run {} {} |>.run {} {}
    docRoleExt.add (roleName, wrapper)
}

/--
Adds a builtin documentation role.

Should be run during initialization.
-/
def addBuiltinDocRole (roleName wrapperName : Name) (impl : DocRoleExpander) : IO Unit :=
  builtinDocRoles.modify (·.alter roleName fun x? => x?.getD #[] |>.push (wrapperName, impl))

builtin_initialize registerBuiltinAttribute {
  name := `builtin_doc_role
  descr := "docstring role expander"
  applicationTime := .afterCompilation
  add := fun decl stx kind => do
    let roleName ←
      if let `(attr|builtin_doc_role $x) := stx then
        realizeGlobalConstNoOverloadWithInfo x
      else
        pure decl
    let argTy := tSyntaxArrayOfCat `inline
    let ret := .app (.const ``Inline [0]) (.const ``ElabInline [])
    let ((wrapper, _), _) ←
      genWrapper decl (some argTy) ret (alsoAccept := #[tSyntaxArrayOfCat ``Parser.inline])
          (view? := roleViewSpec)
        |>.run {} {} |>.run {} {}
    addDeclarationRangesFromSyntax wrapper stx
    declareBuiltin roleName <|
      mkApp3 (.const ``addBuiltinDocRole []) (toExpr roleName) (toExpr wrapper) (.const wrapper [])
    declareBuiltinDocStringAndRanges wrapper
}

builtin_initialize registerBuiltinAttribute {
  name := `doc_code_block
  descr := "docstring code block expander"
  applicationTime := .afterCompilation
  add := fun decl stx kind => do
    checkDocExtMeta decl "code block"
    let blockName ←
      if let `(attr|doc_code_block $x) := stx then
        realizeGlobalConstNoOverloadWithInfo x
      else
        pure decl
    let ret := mkApp2 (.const ``Block [0, 0]) (.const ``ElabInline []) (.const ``ElabBlock [])
    let ((wrapper, _), _) ←
      genWrapper decl (some (.const ``StrLit [])) ret
          (alsoAccept := #[.const ``Lean.Doc.VersoCodeBlock []]) (view? := codeBlockViewSpec)
        |>.run {} {} |>.run {} {}
    docCodeBlockExt.add (blockName, wrapper)
}

/--
Adds a builtin documentation code block.

Should be run during initialization.
-/
def addBuiltinDocCodeBlock (blockName wrapper : Name) (impl : DocCodeBlockExpander) : IO Unit :=
  builtinDocCodeBlocks.modify (·.alter blockName fun x? => x?.getD #[] |>.push (wrapper, impl))

builtin_initialize registerBuiltinAttribute {
  name := `builtin_doc_code_block
  descr := "docstring code block expander"
  applicationTime := .afterCompilation
  add := fun decl stx kind => do
    let blockName ←
      if let `(attr|builtin_doc_code_block $x) := stx then
        realizeGlobalConstNoOverloadWithInfo x
      else
        pure decl
    let ret := mkApp2 (.const ``Block [0, 0]) (.const ``ElabInline []) (.const ``ElabBlock [])
    let ((wrapper, _), _) ←
      genWrapper decl (some (.const ``StrLit [])) ret
          (alsoAccept := #[.const ``Lean.Doc.VersoCodeBlock []]) (view? := codeBlockViewSpec)
        |>.run {} {} |>.run {} {}
    addDeclarationRangesFromSyntax wrapper stx
    declareBuiltin blockName <|
      mkApp3 (.const ``addBuiltinDocCodeBlock [])
        (toExpr blockName) (toExpr wrapper) (.const wrapper [])
    declareBuiltinDocStringAndRanges wrapper
}

/-- A suggestion about an applicable code block -/
structure CodeBlockSuggestion where
  /-- The name of the code block to suggest. -/
  name : Name
  /-- The arguments it should receive, as a string. -/
  args : Option String := none
  /-- More information to show users -/
  moreInfo : Option String := none


builtin_initialize registerBuiltinAttribute {
  name := `doc_code_block_suggestions
  descr := "docstring code block suggestion provider"
  applicationTime := .afterCompilation
  add := fun decl stx kind => do
    let ((name, _), _) ←
      genSuggesterAdapter decl (.const ``StrLit []) (.const ``CodeBlockSuggestion [])
          (alsoAccept := #[.const ``Lean.Doc.VersoCodeBlock []])
        |>.run {} {} |>.run {} {}
    codeBlockSuggestionExt.add name
}

/--
A provider of suggestions for code elements.
-/
abbrev CodeBlockSuggester := StrLit → DocM (Array CodeBlockSuggestion)


/--
Built-in code block suggestions, for bootstrapping
-/
builtin_initialize
  builtinCodeBlockSuggestions : IO.Ref (Array (Name × CodeBlockSuggester)) ← IO.mkRef #[]

/--
Adds a builtin documentation code suggestion provider.

Should be run during initialization.
-/
def addBuiltinCodeBlockSuggestion (decl : Name) (val : CodeBlockSuggester) : IO Unit :=
  builtinCodeBlockSuggestions.modify (·.push (decl, val))

builtin_initialize registerBuiltinAttribute {
  name := `builtin_doc_code_block_suggestions
  descr := "builtin docstring code block suggestion provider"
  applicationTime := .afterCompilation
  add := fun decl stx kind => do
    let ((name, _), _) ←
      genSuggesterAdapter decl (.const ``StrLit []) (.const ``CodeBlockSuggestion [])
          (alsoAccept := #[.const ``Lean.Doc.VersoCodeBlock []])
        |>.run {} {} |>.run {} {}
    declareBuiltin decl <|
      mkApp2 (.const ``addBuiltinCodeBlockSuggestion []) (toExpr decl) (.const name [])
}

builtin_initialize registerBuiltinAttribute {
  name := `doc_directive
  descr := "docstring directive expander"
  applicationTime := .afterCompilation
  add := fun decl stx kind => do
    checkDocExtMeta decl "directive"
    let directiveName ←
      if let `(attr|doc_directive $x) := stx then
        realizeGlobalConstNoOverloadWithInfo x
      else
        pure decl
    let argTy := tSyntaxArrayOfCat `block
    let ret := mkApp2 (.const ``Block [0, 0]) (.const ``ElabInline []) (.const ``ElabBlock [])
    let ((wrapper, _), _) ←
      genWrapper decl (some argTy) ret (alsoAccept := #[tSyntaxArrayOfCat ``Parser.block])
          (view? := directiveViewSpec)
        |>.run {} {} |>.run {} {}
    docDirectiveExt.add (directiveName, wrapper)

}

/--
Adds a builtin documentation directive.

Should be run during initialization.
-/
def addBuiltinDocDirective (directiveName wrapper : Name) (impl : DocDirectiveExpander) : IO Unit :=
  builtinDocDirectives.modify (·.alter directiveName fun x? => x?.getD #[] |>.push (wrapper, impl))

builtin_initialize registerBuiltinAttribute {
  name := `builtin_doc_directive
  descr := "docstring directive expander"
  applicationTime := .afterCompilation
  add := fun decl stx kind => do
    let directiveName ←
      if let `(attr|builtin_doc_directive $x) := stx then
        realizeGlobalConstNoOverloadWithInfo x
      else
        pure decl
    let argTy := tSyntaxArrayOfCat `block
    let ret := mkApp2 (.const ``Block [0, 0]) (.const ``ElabInline []) (.const ``ElabBlock [])
    let ((wrapper, _), _) ←
      genWrapper decl (some argTy) ret (alsoAccept := #[tSyntaxArrayOfCat ``Parser.block])
          (view? := directiveViewSpec)
        |>.run {} {} |>.run {} {}
    addDeclarationRangesFromSyntax wrapper stx
    declareBuiltin directiveName <|
      mkApp3 (.const ``addBuiltinDocDirective [])
        (toExpr directiveName) (toExpr wrapper) (.const wrapper [])
    declareBuiltinDocStringAndRanges wrapper
}

builtin_initialize registerBuiltinAttribute {
  name := `doc_command
  descr := "docstring command expander"
  applicationTime := .afterCompilation
  add := fun decl stx kind => do
    checkDocExtMeta decl "command"
    let commandName ←
      if let `(attr|doc_command $x) := stx then
        realizeGlobalConstNoOverloadWithInfo x
      else
        pure decl

    let ret := mkApp2 (.const ``Block [0, 0]) (.const ``ElabInline []) (.const ``ElabBlock [])
    let ((wrapper, _), _) ←
      genWrapper decl none ret (view? := commandViewSpec) |>.run {} {} |>.run {} {}
    docCommandExt.add (commandName, wrapper)
}

/--
Adds a builtin documentation command.

Should be run during initialization.
-/
def addBuiltinDocCommand (commandName wrapper : Name) (impl : DocCommandExpander) : IO Unit :=
  builtinDocCommands.modify (·.alter commandName fun x? => x?.getD #[] |>.push (wrapper, impl))

builtin_initialize registerBuiltinAttribute {
  name := `builtin_doc_command
  descr := "builtin docstring command expander"
  applicationTime := .afterCompilation
  add := fun decl stx kind => do
    let commandName ←
      if let `(attr|builtin_doc_command $x) := stx then
        realizeGlobalConstNoOverloadWithInfo x
      else
        pure decl

    let ret := mkApp2 (.const ``Block [0, 0]) (.const ``ElabInline []) (.const ``ElabBlock [])
    let ((wrapper, _), _) ←
      genWrapper decl none ret (view? := commandViewSpec) |>.run {} {} |>.run {} {}
    addDeclarationRangesFromSyntax wrapper stx
    declareBuiltin commandName <|
      mkApp3 (.const ``addBuiltinDocCommand [])
        (toExpr commandName) (toExpr wrapper) (.const wrapper [])
    declareBuiltinDocStringAndRanges wrapper
}

open Meta in
/--
Generates the wrapper for a typed Markdown renderer `decl` of type `InlineMdRendererOf X` (or
`BlockMdRendererOf X`) that unpacks the custom element from its `Dynamic`.

Returns the element type's name and the name of the generated wrapper. Errors if the type is not of
the expected form or if `X` has no `TypeName` instance.
-/
private def mkMdRendererWrapper (decl : Name) (isInline : Bool) : MetaM (Name × Name) := do
  let ofName := if isInline then ``Doc.InlineMdRendererOf else ``Doc.BlockMdRendererOf
  let mkName := if isInline then ``Doc.mkInlineMdRenderer else ``Doc.mkBlockMdRenderer
  let wrapperTy := mkConst (if isInline then ``Doc.InlineMdRenderer else ``Doc.BlockMdRenderer)
  let t := (← getConstInfo decl).type
  unless t.isAppOfArity ofName 1 do
    throwError "`{.ofConstName decl}` must have type `{.ofConstName ofName} X` for custom elements of type `X`"
  let elemTy := t.appArg!
  -- The key must match the type name stored in the element's `Dynamic`, which comes from the
  -- `TypeName` instance, so reducible aliases are unfolded to the canonical type name.
  let some key := (← whnfR elemTy).getAppFn.constName?
    | throwError "the custom element type{indentExpr elemTy}\nof `{.ofConstName decl}` must be a named type"
  discard <|
    (try synthInstance (← mkAppM ``TypeName #[elemTy])
     catch _ =>
       throwError m!"the custom element type{indentExpr elemTy}\nof `{.ofConstName decl}` needs a `TypeName` instance." ++ m!"Add `deriving TypeName`".hint')
  let wrapperVal ← mkAppM mkName #[elemTy, mkConst decl]
  let wrapperName := decl ++ `mdRenderer
  addAndCompile (markMeta := isMarkedMeta (← getEnv) decl) <| .defnDecl {
    name := wrapperName, levelParams := [], type := wrapperTy, value := wrapperVal,
    hints := .regular 0, safety := .safe
  }
  return (key, wrapperName)

builtin_initialize registerBuiltinAttribute {
  name := `doc_inline_md
  descr := "Markdown renderer for a docstring inline element of type `InlineMdRendererOf X`"
  applicationTime := .afterCompilation
  add := fun decl _stx _kind => do
    checkDocExtMeta decl "inline Markdown renderer"
    let (key, wrapper) ← (mkMdRendererWrapper decl (isInline := true)).run'
    modifyEnv fun env => docInlineMdExt.addEntry env (key, wrapper)
}

builtin_initialize registerBuiltinAttribute {
  name := `builtin_doc_inline_md
  descr := "builtin Markdown renderer for a docstring inline element"
  applicationTime := .afterCompilation
  add := fun decl _stx _kind => do
    let (key, wrapper) ← (mkMdRendererWrapper decl (isInline := true)).run'
    declareBuiltin wrapper <|
      mkApp2 (.const ``addBuiltinInlineMdRenderer []) (toExpr key) (.const wrapper [])
}

builtin_initialize registerBuiltinAttribute {
  name := `doc_block_md
  descr := "Markdown renderer for a docstring block element of type `BlockMdRendererOf X`"
  applicationTime := .afterCompilation
  add := fun decl _stx _kind => do
    checkDocExtMeta decl "block Markdown renderer"
    let (key, wrapper) ← (mkMdRendererWrapper decl (isInline := false)).run'
    modifyEnv fun env => docBlockMdExt.addEntry env (key, wrapper)
}

builtin_initialize registerBuiltinAttribute {
  name := `builtin_doc_block_md
  descr := "builtin Markdown renderer for a docstring block element"
  applicationTime := .afterCompilation
  add := fun decl _stx _kind => do
    let (key, wrapper) ← (mkMdRendererWrapper decl (isInline := false)).run'
    declareBuiltin wrapper <|
      mkApp2 (.const ``addBuiltinBlockMdRenderer []) (toExpr key) (.const wrapper [])
}
end

unsafe def codeSuggestionsUnsafe : TermElabM (Array CodeSuggester) := do
  let names := (codeSuggestionExt.getState (← getEnv)) |>.toArray
  return (← names.mapM (evalConst _)) ++ (← builtinCodeSuggestions.get).map (·.2)

@[implemented_by codeSuggestionsUnsafe]
opaque codeSuggestions : TermElabM (Array CodeSuggester)

unsafe def codeBlockSuggestionsUnsafe : TermElabM (Array CodeBlockSuggester) := do
  let names := (codeBlockSuggestionExt.getState (← getEnv)) |>.toArray
  return (← names.mapM (evalConst _)) ++ (← builtinCodeBlockSuggestions.get).map (·.2)

@[implemented_by codeBlockSuggestionsUnsafe]
opaque codeBlockSuggestions : TermElabM (Array CodeBlockSuggester)

/--
Resolves a name against `NameMap` that contains a list of builtin expanders, taking into account
open namespaces and the current namespace. This is needed because builtin doc roles/code
blocks/directives are not present in the environment when `Lean` is not imported, so standard name
resolution (`realizeGlobalConstNoOverload`) won't find them.

This is called as a fallback when the identifier can't be resolved.
-/
def resolveBuiltinDocName {α : Type} (builtins : NameMap α) (x : Name) : TermElabM (Option α) := do
  if let some v := builtins.get? x then return some v

  -- Builtins shouldn't require a prefix, as they're part of the language.
  if let some v := builtins.get? (`Lean.Doc ++ x) then return some v

  -- If this fails, try resolving through open namespaces so that {Doc.lit}`foo` will work when
  -- `Lean` is opened.
  let openDecls ← getOpenDecls
  for decl in openDecls do
    match decl with
    | .simple ns exs =>
      if !exs.any (· == x) then
        if let some v := builtins.get? (ns ++ x) then return some v
    | .explicit openedId declName =>
      if openedId == x then
        if let some v := builtins.get? declName then return some v
      else if openedId.isPrefixOf x then
        let candidate := x.replacePrefix openedId declName
        if let some v := builtins.get? candidate then return some v

  -- Try resolving through current namespace hierarchy
  let mut ns ← getCurrNamespace
  while !ns.isAnonymous do
    if let some v := builtins.get? (ns ++ x) then return some v
    ns := ns.getPrefix

  return none

unsafe def roleExpandersForUnsafe (roleName : Ident) :
    TermElabM (Array (Name × DocRoleExpander)) := do
  let x? ←
    try some <$> realizeGlobalConstNoOverload roleName
    catch | _ => pure none
  if let some x := x? then
    let names := (docRoleExt.getState (← getEnv)).get? x |>.getD #[]
    let builtins := (← builtinDocRoles.get).get? x |>.getD #[]
    return (← names.mapM (fun x => do return (x, ← evalConst _ x))) ++ builtins
  else
    -- Builtin roles are not necessarily in the environment at a
    -- quotation site, so they aren't in the preresolved list. They
    -- must also be looked up by their plain name, erasing any macro
    -- scopes a quotation introduced.
    let x := roleName.getId.eraseMacroScopes
    let hasBuiltin ← resolveBuiltinDocName (← builtinDocRoles.get) x
    return hasBuiltin.toArray.flatten


@[implemented_by roleExpandersForUnsafe]
opaque roleExpandersFor (roleName : Ident) :
  TermElabM (Array (Name × DocRoleExpander))

unsafe def codeBlockExpandersForUnsafe (codeBlockName : Ident) :
    TermElabM (Array (Name × DocCodeBlockExpander)) := do
  let x? ←
    try some <$> realizeGlobalConstNoOverload codeBlockName
    catch | _ => pure none
  if let some x := x? then
    let names := (docCodeBlockExt.getState (← getEnv)).get? x |>.getD #[]
    let names' := (← builtinDocCodeBlocks.get).get? x |>.getD #[]
    return (← names.mapM (fun x => do return (x, ← evalConst _ x))) ++ names'
  else
    let x := codeBlockName.getId.eraseMacroScopes
    let hasBuiltin ← resolveBuiltinDocName (← builtinDocCodeBlocks.get) x
    return hasBuiltin.toArray.flatten


@[implemented_by codeBlockExpandersForUnsafe]
opaque codeBlockExpandersFor (codeBlockName : Ident) :
  TermElabM (Array (Name × DocCodeBlockExpander))

unsafe def directiveExpandersForUnsafe (directiveName : Ident) :
    TermElabM (Array (Name × (TSyntaxArray `block → StateT (Array (TSyntax `doc_arg)) DocM (Block ElabInline ElabBlock)))) := do
  let x? ←
    try some <$> realizeGlobalConstNoOverload directiveName
    catch | _ => pure none
  if let some x := x? then
    let names := (docDirectiveExt.getState (← getEnv)).get? x |>.getD #[]
    let names' := (← builtinDocDirectives.get).get? x |>.getD #[]
    return (← names.mapM (fun x => do return (x, ← evalConst _ x))) ++ names'
  else
    let x := directiveName.getId.eraseMacroScopes
    let hasBuiltin ← resolveBuiltinDocName (← builtinDocDirectives.get) x
    return hasBuiltin.toArray.flatten

@[implemented_by directiveExpandersForUnsafe]
opaque directiveExpandersFor (directiveName : Ident) :
  TermElabM (Array (Name × (TSyntaxArray `block → StateT (Array (TSyntax `doc_arg)) DocM (Block ElabInline ElabBlock))))

unsafe def commandExpandersForUnsafe (commandName : Ident) :
    TermElabM (Array (Name × StateT (Array (TSyntax `doc_arg)) DocM (Block ElabInline ElabBlock))) := do
  let x? ←
    try some <$> realizeGlobalConstNoOverload commandName
    catch | _ => pure none
  if let some x := x? then
    let names := (docCommandExt.getState (← getEnv)).get? x |>.getD #[]
    let names' := (← builtinDocCommands.get).get? x |>.getD #[]
    return (← names.mapM (fun x => do return (x, ← evalConst _ x))) ++ names'
  else
    let x := commandName.getId.eraseMacroScopes
    let hasBuiltin :=
      (← builtinDocCommands.get).get? x <|> (← builtinDocCommands.get).get? (`Lean.Doc ++ x)
    return hasBuiltin.toArray.flatten

@[implemented_by commandExpandersForUnsafe]
opaque commandExpandersFor (commandName : Ident) :
  TermElabM (Array (Name × StateT (Array (TSyntax `doc_arg)) DocM (Block ElabInline ElabBlock)))


def mkArgVal (arg : TSyntax ``Parser.argVal) : DocM Term :=
  match ArgValView.of arg with
  | some (.name n) => pure n
  | some (.num n _) => pure n
  | some (.str s _) => pure s
  | none => throwErrorAt arg "Didn't understand as argument value"

def mkArg (arg : TSyntax `doc_arg) : DocM (TSyntax ``Parser.Term.argument) := do
  match ArgView.of arg with
  | some (.anon _ v) =>
    let x ← mkArgVal v
    `(Parser.Term.argument| $x:term)
  | some (.flag _ _ x true) =>
    `(Parser.Term.argument| ($x := true))
  | some (.flag _ _ x false) =>
    `(Parser.Term.argument| ($x := false))
  | some (.named _ (some _) x _ v) =>
    let v ← mkArgVal v
    `(Parser.Term.argument| ($x := $v))
  | some (.named _ none x _ v) =>
    logWarningAt arg "Obsolete syntax" -- TODO suggestion
    let v ← mkArgVal v
    `(Parser.Term.argument| ($x := $v))
  | none => throwErrorAt arg "Didn't understand as argument"

def mkAppStx (name : Ident) (args : TSyntaxArray `doc_arg) : DocM Term := do
  return ⟨mkNode ``Parser.Term.app #[name, mkNullNode (← args.mapM mkArg)]⟩

/--
If `true`, suggestions are provided for code elements.
-/
register_builtin_option doc.verso.suggestions : Bool := {
  defValue := true
  descr := "whether to provide suggestions for code elements"
}

-- Normally, name suggestions should be provided relative to the current scope. But
-- during bootstrapping, the names in question may not yet be defined, so builtin
-- names need special handling.
def suggestionName (name : Name) : TermElabM Name := do
  let name' ←
    -- Builtin expander names never need namespacing
    if (← builtinDocRoles.get).contains name then pure (some name)
    else if (← builtinDocCodeBlocks.get).contains name then pure (some name)
    else pure none
  match name' with
    | some (.str _ s) =>
      -- Check if the simple name is shadowed locally or globally
      let simpleName := .str .anonymous s
      let qualifiedBuiltin := `Lean.Doc ++ simpleName
      -- Local shadowing check
      if (← resolveLocalName simpleName).isSome then
        return qualifiedBuiltin
      -- Global shadowing check: try to resolve the simple name and see
      -- if it resolves to something other than the builtin role
      else
        let resolved? ← try
          some <$> resolveGlobalConstNoOverload (mkIdent simpleName)
        catch _ => pure none
        match resolved? with
        | some resolved =>
          -- If it resolves to the builtin, use simple name; otherwise qualified
          if resolved == qualifiedBuiltin then return simpleName
          else return qualifiedBuiltin
        | none =>
          -- Nothing to shadow
          return simpleName
    | some n => return n
    | none =>
      -- If it exists, unresolve it
      if (← getEnv).contains name then
        unresolveNameGlobalAvoidingLocals name
      else
        -- Fall back to doing nothing
        pure name

def sortSuggestions (ss : Array Meta.Hint.Suggestion) : Array Meta.Hint.Suggestion :=
  let cmp : (x y : Meta.Tactic.TryThis.SuggestionText) → Bool
    | .string s1, .string s2 => s1 < s2
    | .string _, _ => true
    | .tsyntax _, .string _ => false
    | .tsyntax s1, .tsyntax s2 => toString s1.raw < toString s2.raw
  ss.qsort (cmp ·.suggestion ·.suggestion)

open Diff in
def mkSuggestion
    (ref : Syntax) (hintTitle : MessageData)
    (newStrings : Array (String × Option String × Option String)) :
    DocM MessageData := do
  match (← read).suggestionMode with
  | .interactive =>
    hintTitle.hint (newStrings.map fun (s, preInfo?, postInfo?) =>
      { suggestion := s, preInfo?, postInfo? }) (ref? := some ref)
  | .batch =>
    let some ⟨b, e⟩ := ref.getRange?
      | pure m!""
    let text ← getFileMap
    let pre := String.Pos.Raw.extract text.source 0 b
    let post := String.Pos.Raw.extract text.source e text.source.rawEndPos
    let edits := newStrings.map fun (s, _, _) =>
      let lines := text.source.split '\n' |>.toStringArray
      let s' := pre ++ s ++ post
      let lines' := s'.split '\n' |>.toStringArray
      let d := diff lines lines'
      toMessageData <| Diff.linesToString <| d.filter (·.1 != Action.skip)
    pure m!"\n\nHint: {hintTitle}\n{indentD <| m!"\n".joinSep edits.toList}"

def nameOrBuiltinName [Monad m] [MonadEnv m] (x : Name) : m Name := do
  let env ← getEnv
  if env.contains x then return x
  else return `Lean.Doc ++ x

/--
Finds registered expander names that `x` is a suffix of, for use in error message hints when the
name is shadowed. Returns display names suitable for `mkSuggestion`.
-/
def findShadowedNames {α : Type}
    (nonBuiltIns : NameMap (Array Name)) (builtins : NameMap α) (x : Name) :
    TermElabM (Array Name) := do
  if x.isAnonymous then return #[]
  let mut candidates : NameSet := {}
  for (fullName, _) in nonBuiltIns do
    if x.isSuffixOf fullName then
      candidates := candidates.insert fullName
  for (fullName, _) in builtins do
    if x.isSuffixOf fullName then
      candidates := candidates.insert fullName
  let mut result := #[]
  for c in candidates do
    let displayName ← suggestionName c
    -- Only suggest if the display name differs from what the user wrote
    if displayName != x then
      result := result.push displayName
  return result

/--
Builds a hint for an "Unknown role/directive/..." error when the name might be shadowed.
-/
def shadowedHint {α : Type}
    (envEntries : NameMap (Array Name)) (builtins : NameMap α)
    (name : Ident) (kind : String) : DocM MessageData := do
  let candidates ← findShadowedNames envEntries builtins name.getId
  if candidates.isEmpty then return m!""
  let ss := candidates.map fun c => (c.toString, none, none)
  mkSuggestion name m!"`{name}` shadows a {kind}. Use the full name of the shadowed {kind}:" ss

/--
Throws an appropriate error for an unknown doc element (role/directive/code block/command).
Distinguishes "name resolves but isn't registered" from "name doesn't resolve at all",
and includes shadowed-name suggestions when applicable.
-/
def throwUnknownDocElem {α β : Type}
    (envEntries : NameMap (Array Name)) (builtins : NameMap α)
    (name : Ident) (kind : String) : DocM β := do
  let hint ← shadowedHint envEntries builtins name kind
  let resolved? ← try some <$> realizeGlobalConstNoOverload name catch | _ => pure none
  if let some resolved := resolved? then
    let info ← getConstInfo resolved
    throwErrorAt name m!"`{name} : {info.type}` is not registered as a {kind}{hint}"
  else
    throwErrorAt name m!"Unknown {kind} `{name}`{hint}"

/--
Returns the name of a footnote or link reference.
-/
private def refName (name : VersoRefName) : DocM String := do
  -- The parser reads a name with `refNameFn`, which allows the same set of characters as these. If
  -- this exception is thrown, it's due to metaprograms behaving badly.
  let str := name.getVersoRefName
  if str.isEmpty then
    throwErrorAt name "A reference name may not be empty"
  if let some c := (str.find? (!Doc.Parser.isRefNameChar ·)).map (·.get!) then
    throwErrorAt name m!"A reference name may not contain {repr c}"
  return str

/--
Elaborates the syntax of an inline document element to an actual inline document element.
-/
public partial def elabInline (stx : TSyntax ``Parser.inline) :
    DocM (Inline ElabInline) :=
  withRef stx <|
  withInfoContext (mkInfo := pure <| .ofDocInfo {elaborator := decl_name%, stx := stx}) do
  let some v := InlineView.of stx
    | logErrorAt stx m!"Unsupported syntax {stx}"
      return .empty
  match v with
  | .text v =>
    return .text v.getVersoText
  | .emph { content, .. } =>
    return .emph (← content.mapM elabInline)
  | .bold { content, ..} =>
    return .bold (← content.mapM elabInline)
  | .link { content, target := .url _ _ url _, .. } =>
    return .link (← content.mapM elabInline) url.getVersoLinkUrl
  | .link { content, target := .ref _ _ name _, .. } =>
    return .other (delayLink name) (← content.mapM elabInline)
  | .image { alt, target := .url _ _ url _, .. } =>
    -- TODO forward ref to URL
    return .image alt.getVersoImageAlt url.getVersoLinkUrl
  | .image { alt, target := .ref _ _ name _, .. } =>
    return .other (delayImage alt.getVersoImageAlt name) #[]
  | .footnote { name, .. } =>
    return .other (delayFootnote name) #[]
  | .linebreak v =>
    return .linebreak v.newline.getAtomVal
  | .code v =>
    let content := v.content
    let code := v.getVersoCode
    if doc.verso.suggestions.get (← getOptions) then
      if let some ⟨b, e⟩ := stx.raw.getRange? then
        let s := strLitOfContent code content
        let suggesters ← codeSuggestions
        let mut suggestions := #[]
        for suggest in suggesters do
          try suggestions := suggestions ++ (← withEnableInfoTree false <| suggest s)
          catch | _ => pure ()
        unless suggestions.isEmpty do
          let text ← getFileMap
          let str := String.Pos.Raw.extract text.source b e
          let ss : Array (String × Option String × Option String) ←
            suggestions.mapM fun {role, args, moreInfo} => do
              pure {
                fst :=
                  "{" ++ (← suggestionName role).toString ++
                  (args.map (" " ++ ·)).getD "" ++ "}" ++ str,
                snd.fst := none
                snd.snd := moreInfo.map withSpace
              }
          let ss := ss.qsort (fun x y => x.1 < y.1)
          let litName ← suggestionName `Lean.Doc.lit
          let litSuggestion :=
            ( "{" ++ litName.toString ++ "}" ++ str,
              some "Use the `lit` role:\n",
              some "\nto mark the code as literal text and disable suggestions" )
          let ss := ss.push litSuggestion
          let hint ← mkSuggestion stx m!"Insert a role to document it:" ss
          logWarning m!"Code element could be more specific.{hint}"
    return .code code
  | .math v =>
    return .math v.mode v.getVersoCode
  | .role { name, args, content, .. } =>
    let expanders ← roleExpandersFor name
    for (exName, ex) in expanders do
      try
        let res ← ex (asInlineCat content) (asArgCat args) <&> (·.1)
        pushInfoLeaf <| .ofDocElabInfo {
          elaborator := exName,
          stx := name,
          name := exName,
          kind := .role
        }
        return res
      catch
        | e@(.internal id _) =>
          if id == unsupportedSyntaxExceptionId then
            continue
          else throw e
        | e => throw e
    throwUnknownDocElem (docRoleExt.getState (← getEnv)) (← builtinDocRoles.get) name "role"
where
  withSpace (s : String) : String :=
    if s.startsWith " " then s else " " ++ s

/--
Elaborates the syntax of an block-level document element to an actual block-level document element.
-/
public partial def elabBlock (stx : TSyntax ``Parser.block) :
    DocM (Block ElabInline ElabBlock) :=
  withRef stx <|
  withInfoContext (mkInfo := pure <| .ofDocInfo {elaborator := decl_name%, stx := stx}) do
  let some v := BlockView.of stx
    | logErrorAt stx m!"Unsupported syntax: {stx}"
      return .empty
  match v with
  | .para { content, .. } =>
    .para <$> content.mapM elabInline
  | .blockquote { content, .. } =>
    .blockquote <$> content.mapM elabBlock
  | .ul { items, .. } =>
    .ul <$> items.mapM fun item =>
      .mk <$> item.contents.mapM elabBlock
  | .ol { start, items, .. } =>
    .ol start <$> items.mapM fun item =>
      .mk <$> item.contents.mapM elabBlock
  | .dl { items, .. } =>
    .dl <$> items.mapM fun item =>
      withRef item.stx do
        return .mk (← item.term.mapM elabInline) (← item.desc.mapM elabBlock)
  | .footnoteRef v =>
    let refStr ← refName v.name
    if (← getThe InternalState).footnotes.contains refStr then
      throwErrorAt v.name m!"Reference already found"
    else
      let content ← v.content.mapM elabInline
      modifyThe InternalState fun st =>
        { st with
          footnotes :=
            st.footnotes.insert refStr { content := .concat content, location := v.name } }
    return .empty
  | .linkRef v =>
    let refStr ← refName v.name
    if (← getThe InternalState).urls.contains refStr then
      throwErrorAt v.name m!"Reference already found"
    else
      modifyThe InternalState fun st =>
        { st with
          urls := st.urls.insert refStr { content := v.getUrl, location := v.name } }
    return .empty
  | .directive { name, args, content, .. } =>
    let expanders ← directiveExpandersFor name
    for (exName, ex) in expanders do
      try
        let res ← ex (asBlockCat content) (asArgCat args) <&> (·.1)
        pushInfoLeaf <| .ofDocElabInfo {
          elaborator := exName,
          stx := name,
          name := exName,
          kind := .directive
        }
        return res
      catch
        | e@(.internal id _) =>
          if id == unsupportedSyntaxExceptionId then
            continue
          else throw e
        | e => throw e
    throwUnknownDocElem (docDirectiveExt.getState (← getEnv)) (← builtinDocDirectives.get) name "directive"
  | .codeblock { name? := none, openFence := opener,  content, .. } =>
    let s := strLitOfContent content.getVersoCodeBlock content
    if doc.verso.suggestions.get (← getOptions) then
      if let some ⟨b, e⟩ := opener.raw.getRange? then
        let suggesters ← codeBlockSuggestions
        let mut suggestions := #[]
        for suggest in suggesters do
          try suggestions := suggestions ++ (← withEnableInfoTree false <| suggest s)
          catch | _ => pure ()
        unless suggestions.isEmpty do
          let text ← getFileMap
          let str := String.Pos.Raw.extract text.source b e
          let ss : Array (String × Option String × Option String) ←
            suggestions.mapM fun {name, args, moreInfo} => do
              pure {
                fst :=
                  str ++ (← suggestionName name).toString ++
                  (args.map (" " ++ ·)).getD "",
                snd.fst := moreInfo.map withSpace
                snd.snd := none
              }
          let ss := ss.qsort (fun x y => x.1 < y.1)
          let hint ← mkSuggestion opener m!"Insert a specific kind of code block:" ss
          logWarning m!"Code block could be more specific.{hint}"
    return .code s.getString
  | .codeblock { name? := some name, args, content, .. } =>
    let s := strLitOfContent content.getVersoCodeBlock content
    let expanders ← codeBlockExpandersFor name
    for (exName, ex) in expanders do
      try
        let res ← ex s (asArgCat args) <&> (·.1)
        pushInfoLeaf <| .ofDocElabInfo {
          elaborator := exName,
          stx := name,
          name := exName,
          kind := .codeBlock
        }
        return res
      catch
        | e@(.internal id _) =>
          if id == unsupportedSyntaxExceptionId then
            continue
          else throw e
        | e => throw e
    throwUnknownDocElem (docCodeBlockExt.getState (← getEnv)) (← builtinDocCodeBlocks.get) name "code block"
  | .command { name, args, .. } =>
    let expanders ← commandExpandersFor name
    for (exName, ex) in expanders do
      try
        let res ← ex (asArgCat args) <&> (·.1)
        pushInfoLeaf <| .ofDocElabInfo {
          elaborator := exName,
          stx := name,
          name := exName,
          kind := .command
        }
        return res
      catch
        | e@(.internal id _) =>
          if id == unsupportedSyntaxExceptionId then
            continue
          else throw e
        | e => throw e
    throwUnknownDocElem (docCommandExt.getState (← getEnv)) (← builtinDocCommands.get) name "document command"
  | .metadata .. =>
    let h ←
      if stx.raw.getRange?.isSome then m!"Remove it".hint #[""] (ref? := stx)
      else pure m!""
    logError m!"Part metadata is not supported in docstrings.{h}"
    return .empty
  | .header .. => throwErrorAt stx "Unsupported syntax: {stx}"
where
  withSpace (s : String) : String :=
    if s.endsWith " " then s else s ++ " "

def takeFirst? (xs : Array α) : Option (α × Array α) :=
  if h : xs.size > 0 then
    some (xs[0], xs.extract 1)
  else none

partial def elabBlocks' (level : Nat) :
    StateT (TSyntaxArray ``Parser.block) DocM
      (Array (Block ElabInline ElabBlock) × Array (Part ElabInline ElabBlock Empty)) := do
  let mut pre := #[]
  let mut sub := #[]
  repeat
    let blocks ← getThe (TSyntaxArray ``Parser.block)
    if let some (x, xs) := takeFirst? blocks then
      if let some (.header { level := n, content := headerName, .. }) := BlockView.of x then
        if n < level then return (pre, sub)
        else if n = level then
          set xs
          let (content, subParts) ← elabBlocks' (level + 1)
          let title ←
            liftM <| withInfoContext (mkInfo := pure <| .ofDocInfo {elaborator := `no_elab, stx := x}) <|
              headerName.mapM elabInline
          let mdTitle ← MarkdownM.run' (ToMarkdown.toMarkdown (Inline.concat title))
          sub := sub.push {
            title,
            titleString := mdTitle
            metadata := none
            content, subParts
          }
        else
          logErrorAt x m!"Expected a header no deeper than `{"".pushn '#' <| level + 1}`"
          set xs
      else
        set xs
        try
          pre := pre.push (← elabBlock x)
        catch
          | e =>
            logErrorAt e.getRef e.toMessageData
    else
      break
  return (pre, sub)

def elabModSnippet'
    (range : DeclarationRange) (level : Nat)
    (blocks : TSyntaxArray ``Parser.block) :
    DocM VersoModuleDocs.Snippet := do
  let mut snippet : VersoModuleDocs.Snippet := {
    declarationRange := range
  }
  let mut maxLevel := level
  for b in blocks do
    if let some (.header { level := n, content, .. }) := BlockView.of b then
        if n > maxLevel then
          logErrorAt b m!"Incorrect header nesting: expected at most `{"#".pushn '#' maxLevel}` \
            but got `{"#".pushn '#' n}`"
        else
          maxLevel := n + 1
          let title ←
            liftM <| withInfoContext (mkInfo := pure <| .ofDocInfo {elaborator := `no_elab, stx := b}) <|
              content.mapM elabInline
          let some headerRange ← getDeclarationRange? b
            | throwErrorAt b "Can't find header source position"
          let mdTitle ← MarkdownM.run' (ToMarkdown.toMarkdown (Inline.concat title))
          snippet := snippet.addPart n headerRange {
            title,
            titleString := mdTitle
            metadata := none, content := #[], subParts := #[]
          }
      else
        snippet := snippet.addBlock (← elabBlock b)
  return snippet

partial def fixupInline (inl : Inline ElabInline) : DocM (Inline ElabInline) := do
  match inl with
  | .concat xs => .concat <$> xs.mapM fixupInline
  | .emph xs => .emph <$> xs.mapM fixupInline
  | .bold xs => .bold <$> xs.mapM fixupInline
  | .link content url => (.link · url) <$> content.mapM fixupInline
  | .footnote name content => .footnote name <$> content.mapM fixupInline
  | .text s => pure (.text s)
  | .image alt url => pure (.image alt url)
  | .code s => pure (.code s)
  | .math mode s => pure (.math mode s)
  | .linebreak s => pure (.linebreak s)
  | .other i xs =>
    let some val := getCustom i
      | .other i <$> xs.mapM fixupInline
    if let some { name } := val.get? ElabLink then
      let nameStr ← refName name
      if let some r@{content := url, seen, .. } := (← getThe InternalState).urls[nameStr]? then
        unless seen do modifyThe InternalState fun st => { st with urls := st.urls.insert nameStr { r with seen := true } }
        return .link (← xs.mapM fixupInline) url
      else
        logErrorAt name "Reference not found"
        return .concat (← xs.mapM fixupInline)
    else if let some { alt, name } := val.get? ElabImage then
      let nameStr ← refName name
      if let some r@{content := url, seen, ..} := (← getThe InternalState).urls[nameStr]? then
        unless seen do modifyThe InternalState fun st => { st with urls := st.urls.insert nameStr { r with seen := true } }
        return .image alt url
      else
        logErrorAt name "Reference not found"
        return .empty
    else if let some { name } := val.get? ElabFootnote then
      let nameStr ← refName name
      if let some r@{ content, seen, .. } := (← getThe InternalState).footnotes[nameStr]? then
        unless seen do modifyThe InternalState fun st =>
          { st with footnotes := st.footnotes.insert nameStr { r with seen := true } }
        return .footnote nameStr #[← fixupInline content]
      else
        logErrorAt name "Footnote not found"
        return .empty
    else
      .other i <$> xs.mapM fixupInline
where
  getCustom : ElabInline → Option Dynamic
    | .custom c => some c
    | .deferred _ => none

partial def fixupBlock (block : Block ElabInline ElabBlock) : DocM (Block ElabInline ElabBlock) := do
  match block with
  | .para xs => .para <$> xs.mapM fixupInline
  | .concat xs => .concat <$> xs.mapM fixupBlock
  | .blockquote xs => .blockquote <$> xs.mapM fixupBlock
  | .dl xs => .dl <$> xs.mapM fun { term, desc } => do
    let term ← term.mapM fixupInline
    let desc ← desc.mapM fixupBlock
    pure { term, desc }
  | .ul xs => .ul <$> xs.mapM fun ⟨bs⟩ => do return ⟨← bs.mapM fixupBlock⟩
  | .ol n xs => .ol n <$> xs.mapM fun ⟨bs⟩ => do return ⟨← bs.mapM fixupBlock⟩
  | .code s => pure (.code s)
  | .other i xs => .other i <$> xs.mapM fixupBlock

partial def fixupPart (part : Part ElabInline ElabBlock Empty) : DocM (Part ElabInline ElabBlock Empty) := do
  return { part with
    title := ← part.title.mapM fixupInline
    content := ← part.content.mapM fixupBlock,
    subParts := ← part.subParts.mapM fixupPart
  }


partial def fixupBlocks : (Array (Block ElabInline ElabBlock) × Array (Part ElabInline ElabBlock Empty)) → DocM (Array (Block ElabInline ElabBlock) × Array (Part ElabInline ElabBlock Empty))
  | (bs, ps) => do
    let bs ← bs.mapM fixupBlock
    let ps ← ps.mapM fixupPart
    return (bs, ps)

partial def fixupSnippet (snippet : VersoModuleDocs.Snippet) : DocM VersoModuleDocs.Snippet := do
  return {snippet with
    text := ← snippet.text.mapM fixupBlock,
    sections := ← snippet.sections.mapM fun (level, range, content) => do
      return (level, range, ← fixupPart content)
  }
/--
After fixing up the references, check to see which were not used and emit a suitable warning.
-/
def warnUnusedRefs : DocM Unit := do
  for (_, {location, seen, ..}) in (← getThe InternalState).urls do
    unless seen do
      logWarningAt location "Unused URL"
  for (_, {location, seen, ..}) in (← getThe InternalState).footnotes do
    unless seen do
      logWarningAt location "Unused footnote"

/-- Elaborates a sequence of blocks into a document. -/
public def elabBlocks (blocks : TSyntaxArray ``Parser.block) :
    DocM (Array (Block ElabInline ElabBlock) × Array (Part ElabInline ElabBlock Empty)) := do
  -- Users should not need to make import needed for embedded terms public
  withoutExporting do
    let (v, _) ← elabBlocks' 0 |>.run blocks
    let res ← fixupBlocks v
    warnUnusedRefs
    return res

/-- Elaborates a sequence of blocks into a module doc snippet. -/
public def elabModSnippet
    (range : DeclarationRange) (blocks : TSyntaxArray ``Parser.block)
    (nestingLevel : Nat) :
    DocM (VersoModuleDocs.Snippet) := do
  let s ← elabModSnippet' range nestingLevel blocks
  let s ← fixupSnippet s
  warnUnusedRefs
  return s

/--
Renders the name of a documentation `extension` (role, code block, directive, or command) for
user-facing messages. Builtins are designated by their last component because users invoke them by
that bare name (e.g. `` {given}`x` ``, rather than `` {Lean.Doc.given}`x` ``), regardless of which
namespaces are open. Non-builtin elements use `MessageData.ofConstName` so they appear in their
shortest unambiguous form.
-/
private def docElementMessage (extension : Name) : BaseIO MessageData := do
  if (← isBuiltin) then
    match extension with
    | .str _ s => return s
    | _ => return .ofConstName extension
  else
    return .ofConstName extension
where
  isBuiltin : BaseIO Bool := do
    return (← builtinDocRoles.get).contains extension ||
      (← builtinDocCodeBlocks.get).contains extension ||
      (← builtinDocDirectives.get).contains extension ||
      (← builtinDocCommands.get).contains extension

/--
Registers a single `MVarErrorInfo` so that, if any metavariable in `e` remains unresolved at the
end of document elaboration, one error is emitted at `ref` naming the documentation `extension` (the
constant implementing the role/code block, e.g. `Lean.Doc.given`) and the supplied `location`
(e.g. "type of variable `xs`") that contained the hole. The element name is rendered via
`docElementMessage`. Roles and code blocks use this to attach a diagnostic to the syntax
that introduced the variable, in addition to the standard placeholder errors that the underlying
elaborator emits for unsolved metas.
-/
public def registerDocMVar (extension : Name) (e : Expr) (ref : Syntax) (location : MessageData) :
    TermElabM Unit := do
  unless (← Meta.getMVars e).isEmpty do
    let elementMsg ← docElementMessage extension
    let anchor ← Meta.mkFreshExprMVar none
    anchor.mvarId!.assign e
    Term.registerMVarErrorCustomInfo anchor.mvarId! ref
      m!"unresolved metavariable in `{elementMsg}` ({location}):{indentExpr e}"
