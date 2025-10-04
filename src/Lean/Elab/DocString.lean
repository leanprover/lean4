/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Thrane Christiansen
-/
module
prelude
public import Lean.ScopedEnvExtension
import Std.Data.HashMap
public import Lean.DocString.Types
public import Lean.Elab.Term.TermElabM
public import Lean.Elab.Command.Scope
import Lean.DocString.Syntax
import Lean.Meta.Hint
import Lean.DocString.Markdown
import Lean.BuiltinDocAttr

set_option linter.missingDocs true

namespace Lean.Doc

open Lean Elab Term
open Std
open scoped Lean.Doc.Syntax


public section

private structure ElabLink where
  name : StrLit
deriving TypeName

private def delayLink (name : StrLit) : ElabInline where
  name := decl_name%
  val := .mk (ElabLink.mk name)

private structure ElabImage where
  alt : String
  name : StrLit
deriving TypeName

private def delayImage (alt : String) (name : StrLit) : ElabInline where
  name := decl_name%
  val := .mk (ElabImage.mk alt name)

private structure ElabFootnote where
  name : StrLit
deriving TypeName

private def delayFootnote (name : StrLit) : ElabInline where
  name := decl_name%
  val := .mk (ElabFootnote.mk name)

private structure Ref (α) where
  content : α
  location : Syntax
  seen := false

/-- The internal state used by docstring elaboration -/
structure InternalState where
  private footnotes : HashMap String (Ref (Inline ElabInline)) := {}
  private urls : HashMap String (Ref String) := {}

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
    let {openDecls, lctx, options, ..} := (← st'.get)
    let v ←
      withTheReader Core.Context (fun ρ => { ρ with openDecls, options }) <|
      withTheReader Meta.Context (fun ρ => { ρ with lctx }) <|
      act
    return v

private structure ModuleDocstringState extends Lean.Doc.State where
  scopedExts : Array (ScopedEnvExtension EnvExtensionEntry EnvExtensionEntry EnvExtensionState)


private builtin_initialize modDocstringStateExt : EnvExtension (Option ModuleDocstringState) ←
  registerEnvExtension (pure none)

private def getModState
    [Monad m] [MonadEnv m] [MonadLiftT IO m] [MonadLCtx m]
    [MonadResolveName m] [MonadOptions m] : m ModuleDocstringState := do
  if let some st := modDocstringStateExt.getState (← getEnv) then
    return st
  else
    let lctx ← getLCtx
    let openDecls ← getOpenDecls
    let options ← getOptions
    let scopes := [{header := "", isPublic := true}]
    let st : ModuleDocstringState := { scopes, openDecls, lctx, options, scopedExts := #[] }
    modifyEnv fun env =>
      modDocstringStateExt.setState env st
    return st

private def setModState [Monad m] [MonadEnv m] (state : ModuleDocstringState) : m Unit := do
  modifyEnv fun env =>
    modDocstringStateExt.setState env state

/--
Runs a documentation elaborator in the module docstring context.
-/
def DocM.execForModule (act : DocM α) (suggestionMode : SuggestionMode := .interactive) :
    TermElabM α := withoutModifyingEnv do
  let sc ← scopedEnvExtensionsRef.get
  let st ← getModState
  try
    scopedEnvExtensionsRef.set st.scopedExts
    let ((v, _), _) ←
      act.run { suggestionMode } |>.run {} |>.run st.toState
    pure v
  finally
    scopedEnvExtensionsRef.set sc

open Lean.Parser.Term in
/--
Runs a documentation elaborator in a declaration's context, discarding changes made to the
environment.
-/
def DocM.exec (declName : Name) (binders : Syntax) (act : DocM α)
    (suggestionMode : SuggestionMode := .interactive) :
    TermElabM α := withoutModifyingEnv do
  let some ci := (← getEnv).constants.find? declName
    | throwError "Unknown constant {declName} when building docstring"
  let st ← Term.saveState
  Core.resetMessageLog -- We'll replay the messages after the elab loop
  try
    let (lctx, localInstances) ← buildContext ci.type binders
    let sc ← scopedEnvExtensionsRef.get
    try
      let openDecls ← getOpenDecls
      let options ← getOptions
      let scopes := [{header := "", isPublic := true}]
      let ((v, _), _) ← withTheReader Meta.Context (fun ρ => { ρ with localInstances }) <|
        act.run { suggestionMode } |>.run {} |>.run { scopes, openDecls, lctx, options }
      pure v
    finally
      scopedEnvExtensionsRef.set sc
  finally
    let msgs ← Core.getMessageLog
    st.restore
    Core.setMessageLog ((← Core.getMessageLog) ++ msgs)
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
          if x'.getId == y then
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
    | _ => throwErrorAt binderStx "Couldn't interpret binder {binderStx}"
  getNames (ids : Syntax) : TermElabM (Array (Option Syntax)) :=
    ids.getArgs.mapM fun x =>
      if x.getKind == identKind || x.getKind == ``hole then
        pure (some x)
      else throwErrorAt x "identifer or `_` expected"


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
@[expose]
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
def DocArg.ofSyntax : TSyntax `arg_val → TermElabM DocArg
  | `(arg_val| $x:ident ) => pure <| .ident x
  | `(arg_val| $x:num ) => pure <| .num x
  | `(arg_val| $x:str ) => pure <| .str x
  | other => throwErrorAt other "Failed to parse argument value"

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
    if let `(doc_arg|$v:arg_val) := args[i] then
      set (σ := Array (TSyntax `doc_arg)) (args[:i] ++ args[i+1:])
      let v ← DocArg.ofSyntax v
      return (← FromDocArg.fromDocArg v)
  throwError "Missing positional argument `{name}`"

private def asNamed : Syntax → Option (Ident × TSyntax `arg_val)
  | `(doc_arg|$x:ident := $v:arg_val) => some (x, v)
  | `(doc_arg|($x:ident := $v:arg_val)) => some (x, v)
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
  asFlag
    | `(doc_arg|+$x:ident) => some (x, true)
    | `(doc_arg|-$x:ident) => some (x, false)
    | _ => none

/--
Asserts that there are no further arguments to a documentation language extension.
-/
protected def done : StateT (Array (TSyntax `doc_arg)) DocM Unit := do
  for arg in (← get) do
    match arg with
    | `(doc_arg|+$x:ident)
    | `(doc_arg|-$x:ident) =>
      logErrorAt arg m!"Unexpected flag `{x.getId}`"
    | `(doc_arg| ($x := $_)) | `(doc_arg| $x:ident := $_) =>
      logErrorAt arg m!"Unexpected named argument `{x.getId}`"
    | `(doc_arg| $_:arg_val) =>
      logErrorAt arg m!"Unexpected positional argument"
    | _ =>
      logErrorAt arg m!"Unexpected argument"
  return

private inductive ArgSpec where
  | positional (name : Name) (type : Expr)
  | named (name : Name) (type : Expr) (default : Expr)
  | many (name : Name) (type : Expr)
  | flag (name : Name) (default : Bool)
deriving Repr

open Meta in
private def genWrapper (declName : Name) (argType : Option Expr) (retType : Expr) : TermElabM Name := do
  if let some c := (← getEnv).constants.find? declName then
    let argSpec ← forallTelescope c.type fun args ret => do
      let mut argSpec : Array ArgSpec := #[]

      for arg in (if argType.isSome then (args[:args.size-1] : Array _) else args) do
        let localDecl ← arg.fvarId!.getDecl
        let name := localDecl.userName
        let argType := localDecl.type
        if argType.isAppOfArity' ``optParam 2 then
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
      if h : args.size < 1 then
        throwError "Expected at least one parameter"
      else
        if let some expected := argType then
          let final := args[args.size-1]
          let localDecl ← final.fvarId!.getDecl
          unless ← isDefEq localDecl.type expected do
            throwError "Expected last parameter type to be {expected} but got {localDecl.type}"

        let expected ← mkAppM ``DocM #[retType]
        unless ← isDefEq ret expected do
          throwError "Expected return type to be {expected} but got {ret}"

      pure argSpec
    let inls ← mkAppM ``TSyntaxArray #[← mkListLit (.const ``SyntaxNodeKind []) [toExpr `inline]]
    let parser ←
      if let some argType := argType then
        withLocalDecl (← mkFreshBinderName) .default argType fun i => do
          mkLambdaFVars #[i] (← build 0 argSpec #[] (some i))
      else build 0 argSpec #[] none
    let parserTy ← inferType parser
    let name ← mkFreshUserName (declName ++ `getArgs)
    let name := declName ++ `getArgs
    addAndCompile <| .defnDecl {
      name
      levelParams := []
      type := parserTy
      value := parser
      hints := .regular 0
      safety := .safe
    }
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
    else
      let last ← mkAppM ``Lean.Doc.done #[]
      let m ← mkAppM ``StateT #[← mkAppM ``Array #[← mkAppM ``TSyntax #[← mkListLit (.const ``SyntaxNodeKind []) [toExpr `doc_arg]]], ← mkAppM ``DocM #[]]
      let k ← withLocalDecl (← mkFreshBinderName) .default (.const ``Unit []) fun u => do
        let args := body.map (args.push ·) |>.getD args
        mkLambdaFVars #[u] (← mkAppOptM ``liftM #[none, some m, none, none, (← mkAppM declName args)])
      mkAppM ``Bind.bind #[last, k]

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
    if let some d := (← getEnv).find? decl then
      if d.type matches (.forallE _ (.const ``StrLit _)
          (.app (.const ``DocM _) (.app (.const ``Array _) (.const ``CodeSuggestion _)))
          .default) then
        codeSuggestionExt.add decl
      else
        throwError "Wrong type for {.ofConstName decl}: {indentD <| repr d.type}"
    else
      throwError "{.ofConstName decl} is not defined"
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
    if let some d := (← getEnv).find? decl then
      if d.type matches (.forallE _ (.const ``StrLit _)
          (.app (.const ``DocM _) (.app (.const ``Array _) (.const ``CodeSuggestion _)))
          .default) then
        declareBuiltin decl <|
          mkApp2 (.const ``addBuiltinCodeSuggestion []) (toExpr decl) (.const decl [])
      else
        throwError "Wrong type for {.ofConstName decl}: {indentD <| repr d.type}"
    else
      throwError "{.ofConstName decl} is not defined"
}

builtin_initialize registerBuiltinAttribute {
  name := `doc_role
  descr := "docstring role expander"
  applicationTime := .afterCompilation
  add := fun decl stx kind => do
    let roleName ←
      if let `(attr|doc_role $x) := stx then
        realizeGlobalConstNoOverloadWithInfo x
      else
        pure decl
    let argTy : Expr :=
      .app (.const ``TSyntaxArray [])
        (mkApp3 (.const ``List.cons [0]) (.const ``SyntaxNodeKind []) (toExpr `inline) (.app (.const ``List.nil [0]) (.const ``SyntaxNodeKind [])))
    let ret := .app (.const ``Inline [0]) (.const ``ElabInline [])
    let ((wrapper, _), _) ← genWrapper decl (some argTy) ret |>.run {} {} |>.run {} {}
    docRoleExt.add (roleName, wrapper)
    if (← findInternalDocString? (← getEnv) decl).isSome then
      addInheritedDocString wrapper decl
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
    let argTy : Expr :=
      .app (.const ``TSyntaxArray [])
        (mkApp3 (.const ``List.cons [0]) (.const ``SyntaxNodeKind []) (toExpr `inline) (.app (.const ``List.nil [0]) (.const ``SyntaxNodeKind [])))
    let ret := .app (.const ``Inline [0]) (.const ``ElabInline [])
    let ((wrapper, _), _) ← genWrapper decl (some argTy) ret |>.run {} {} |>.run {} {}
    addDeclarationRangesFromSyntax wrapper stx
    declareBuiltin roleName <|
      mkApp3 (.const ``addBuiltinDocRole []) (toExpr roleName) (toExpr wrapper) (.const wrapper [])
    if (← findInternalDocString? (← getEnv) decl).isSome then
      addInheritedDocString wrapper decl
    declareBuiltinDocStringAndRanges wrapper
}

builtin_initialize registerBuiltinAttribute {
  name := `doc_code_block
  descr := "docstring code block expander"
  applicationTime := .afterCompilation
  add := fun decl stx kind => do
    let blockName ←
      if let `(attr|doc_code_block $x) := stx then
        realizeGlobalConstNoOverloadWithInfo x
      else
        pure decl
    let ret := mkApp2 (.const ``Block [0, 0]) (.const ``ElabInline []) (.const ``ElabBlock [])
    let ((wrapper, _), _) ← genWrapper decl (some (.const ``StrLit [])) ret |>.run {} {} |>.run {} {}
    docCodeBlockExt.add (blockName, wrapper)
    if (← findInternalDocString? (← getEnv) decl).isSome then
      addInheritedDocString wrapper decl
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
    let ((wrapper, _), _) ← genWrapper decl (some (.const ``StrLit [])) ret |>.run {} {} |>.run {} {}
    addDeclarationRangesFromSyntax wrapper stx
    declareBuiltin blockName <|
      mkApp3 (.const ``addBuiltinDocCodeBlock [])
        (toExpr blockName) (toExpr wrapper) (.const wrapper [])
    if (← findInternalDocString? (← getEnv) decl).isSome then
      addInheritedDocString wrapper decl
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
    if let some d := (← getEnv).find? decl then
      if d.type matches (.forallE _ (.const ``StrLit _)
          (.app (.const ``DocM _) (.app (.const ``Array _) (.const ``CodeBlockSuggestion _)))
          .default) then
        codeBlockSuggestionExt.add decl
      else
        throwError "Wrong type for {.ofConstName decl}: {indentD <| repr d.type}"
    else
      throwError "{.ofConstName decl} is not defined"
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
    if let some d := (← getEnv).find? decl then
      if d.type matches (.forallE _ (.const ``StrLit _)
          (.app (.const ``DocM _) (.app (.const ``Array _) (.const ``CodeBlockSuggestion _)))
          .default) then
        declareBuiltin decl <|
          mkApp2 (.const ``addBuiltinCodeBlockSuggestion []) (toExpr decl) (.const decl [])
      else
        throwError "Wrong type for {.ofConstName decl}: {indentD <| repr d.type}"
    else
      throwError "{.ofConstName decl} is not defined"
}

builtin_initialize registerBuiltinAttribute {
  name := `doc_directive
  descr := "docstring directive expander"
  applicationTime := .afterCompilation
  add := fun decl stx kind => do
    let directiveName ←
      if let `(attr|doc_directive $x) := stx then
        realizeGlobalConstNoOverloadWithInfo x
      else
        pure decl
    let argTy : Expr :=
      .app (.const ``TSyntaxArray [])
        (mkApp3 (.const ``List.cons [0]) (.const ``SyntaxNodeKind []) (toExpr `block) (.app (.const ``List.nil [0]) (.const ``SyntaxNodeKind [])))
    let ret := mkApp2 (.const ``Block [0, 0]) (.const ``ElabInline []) (.const ``ElabBlock [])
    let ((wrapper, _), _) ← genWrapper decl (some argTy) ret |>.run {} {} |>.run {} {}
    docDirectiveExt.add (directiveName, wrapper)
    if (← findInternalDocString? (← getEnv) decl).isSome then
      addInheritedDocString wrapper decl

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
    let argTy : Expr :=
      .app (.const ``TSyntaxArray [])
        (mkApp3 (.const ``List.cons [0]) (.const ``SyntaxNodeKind []) (toExpr `block) (.app (.const ``List.nil [0]) (.const ``SyntaxNodeKind [])))
    let ret := mkApp2 (.const ``Block [0, 0]) (.const ``ElabInline []) (.const ``ElabBlock [])
    let ((wrapper, _), _) ← genWrapper decl (some argTy) ret |>.run {} {} |>.run {} {}
    addDeclarationRangesFromSyntax wrapper stx
    declareBuiltin directiveName <|
      mkApp3 (.const ``addBuiltinDocDirective [])
        (toExpr directiveName) (toExpr wrapper) (.const wrapper [])
    if (← findInternalDocString? (← getEnv) decl).isSome then
      addInheritedDocString wrapper decl
    declareBuiltinDocStringAndRanges wrapper
}

builtin_initialize registerBuiltinAttribute {
  name := `doc_command
  descr := "docstring command expander"
  applicationTime := .afterCompilation
  add := fun decl stx kind => do
    let commandName ←
      if let `(attr|doc_command $x) := stx then
        realizeGlobalConstNoOverloadWithInfo x
      else
        pure decl

    let ret := mkApp2 (.const ``Block [0, 0]) (.const ``ElabInline []) (.const ``ElabBlock [])
    let ((wrapper, _), _) ← genWrapper decl none ret |>.run {} {} |>.run {} {}
    docCommandExt.add (commandName, wrapper)
    if (← findInternalDocString? (← getEnv) decl).isSome then
      addInheritedDocString wrapper decl
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
    let ((wrapper, _), _) ← genWrapper decl none ret |>.run {} {} |>.run {} {}
    addDeclarationRangesFromSyntax wrapper stx
    declareBuiltin commandName <|
      mkApp3 (.const ``addBuiltinDocCommand [])
        (toExpr commandName) (toExpr wrapper) (.const wrapper [])
    if (← findInternalDocString? (← getEnv) decl).isSome then
      addInheritedDocString wrapper decl
    declareBuiltinDocStringAndRanges wrapper
}
end

private unsafe def codeSuggestionsUnsafe : TermElabM (Array (StrLit → DocM (Array CodeSuggestion))) := do
  let names := (codeSuggestionExt.getState (← getEnv)) |>.toArray
  return (← names.mapM (evalConst _)) ++ (← builtinCodeSuggestions.get).map (·.2)

@[implemented_by codeSuggestionsUnsafe]
private opaque codeSuggestions : TermElabM (Array (StrLit → DocM (Array CodeSuggestion)))

private unsafe def codeBlockSuggestionsUnsafe : TermElabM (Array (StrLit → DocM (Array CodeBlockSuggestion))) := do
  let names := (codeBlockSuggestionExt.getState (← getEnv)) |>.toArray
  return (← names.mapM (evalConst _)) ++ (← builtinCodeBlockSuggestions.get).map (·.2)

@[implemented_by codeBlockSuggestionsUnsafe]
private opaque codeBlockSuggestions : TermElabM (Array (StrLit → DocM (Array CodeBlockSuggestion)))

private def builtinElabName (n : Name) : Option Name :=
  if (`Lean.Doc).isPrefixOf n then some n
  else if n matches (.str .anonymous _) then some <| `Lean.Doc ++ n
  else none

private unsafe def roleExpandersForUnsafe (roleName : Ident) :
    TermElabM (Array (Name × (TSyntaxArray `inline → StateT (Array (TSyntax `doc_arg)) DocM (Inline ElabInline)))) := do
  let x? ←
    try some <$> realizeGlobalConstNoOverload roleName
    catch | _ => pure none
  if let some x := x? then
    let names := (docRoleExt.getState (← getEnv)).get? x |>.getD #[]
    let builtins := (← builtinDocRoles.get).get? x |>.getD #[]
    return (← names.mapM (fun x => do return (x, ← evalConst _ x))) ++ builtins
  else
    let x := roleName.getId
    let hasBuiltin :=
      (← builtinDocRoles.get).get? x <|> (← builtinDocRoles.get).get? (`Lean.Doc ++ x)
    return hasBuiltin.toArray.flatten


@[implemented_by roleExpandersForUnsafe]
private opaque roleExpandersFor (roleName : Ident) :
  TermElabM (Array (Name × (TSyntaxArray `inline → StateT (Array (TSyntax `doc_arg)) DocM (Inline ElabInline))))

private unsafe def codeBlockExpandersForUnsafe (codeBlockName : Ident) :
    TermElabM (Array (Name × (StrLit → StateT (Array (TSyntax `doc_arg)) DocM (Block ElabInline ElabBlock)))) := do
  let x? ←
    try some <$> realizeGlobalConstNoOverload codeBlockName
    catch | _ => pure none
  if let some x := x? then
    let names := (docCodeBlockExt.getState (← getEnv)).get? x |>.getD #[]
    let names' := (← builtinDocCodeBlocks.get).get? x |>.getD #[]
    return (← names.mapM (fun x => do return (x, ← evalConst _ x))) ++ names'
  else
    let x := codeBlockName.getId
    let hasBuiltin :=
      (← builtinDocCodeBlocks.get).get? x <|> (← builtinDocCodeBlocks.get).get? (`Lean.Doc ++ x)
    return hasBuiltin.toArray.flatten


@[implemented_by codeBlockExpandersForUnsafe]
private opaque codeBlockExpandersFor (codeBlockName : Ident) :
  TermElabM (Array (Name × (StrLit → StateT (Array (TSyntax `doc_arg)) DocM (Block ElabInline ElabBlock))))

private unsafe def directiveExpandersForUnsafe (directiveName : Ident) :
    TermElabM (Array (Name × (TSyntaxArray `block → StateT (Array (TSyntax `doc_arg)) DocM (Block ElabInline ElabBlock)))) := do
  let x? ←
    try some <$> realizeGlobalConstNoOverload directiveName
    catch | _ => pure none
  if let some x := x? then
    let names := (docDirectiveExt.getState (← getEnv)).get? x |>.getD #[]
    let names' := (← builtinDocDirectives.get).get? x |>.getD #[]
    return (← names.mapM (fun x => do return (x, ← evalConst _ x))) ++ names'
  else
    let x := directiveName.getId
    let hasBuiltin :=
      (← builtinDocDirectives.get).get? x <|> (← builtinDocDirectives.get).get? (`Lean.Doc ++ x)
    return hasBuiltin.toArray.flatten

@[implemented_by directiveExpandersForUnsafe]
private opaque directiveExpandersFor (directiveName : Ident) :
  TermElabM (Array (Name × (TSyntaxArray `block → StateT (Array (TSyntax `doc_arg)) DocM (Block ElabInline ElabBlock))))

private unsafe def commandExpandersForUnsafe (commandName : Ident) :
    TermElabM (Array (Name × StateT (Array (TSyntax `doc_arg)) DocM (Block ElabInline ElabBlock))) := do
  let x? ←
    try some <$> realizeGlobalConstNoOverload commandName
    catch | _ => pure none
  if let some x := x? then
    let names := (docCommandExt.getState (← getEnv)).get? x |>.getD #[]
    let names' := (← builtinDocCommands.get).get? x |>.getD #[]
    return (← names.mapM (fun x => do return (x, ← evalConst _ x))) ++ names'
  else
    let x := commandName.getId
    let hasBuiltin :=
      (← builtinDocCommands.get).get? x <|> (← builtinDocCommands.get).get? (`Lean.Doc ++ x)
    return hasBuiltin.toArray.flatten

@[implemented_by commandExpandersForUnsafe]
private opaque commandExpandersFor (commandName : Ident) :
  TermElabM (Array (Name × StateT (Array (TSyntax `doc_arg)) DocM (Block ElabInline ElabBlock)))


private def mkArgVal (arg : TSyntax `arg_val) : DocM Term :=
  match arg with
  | `(arg_val|$n:ident) => pure n
  | `(arg_val|$n:num) => pure n
  | `(arg_val|$s:str) => pure s
  | _ => throwErrorAt arg "Didn't understand as argument value"

private def mkArg (arg : TSyntax `doc_arg) : DocM (TSyntax ``Parser.Term.argument) := do
  match arg with
  | `(doc_arg|$x:arg_val) =>
    let x ← mkArgVal x
    `(Parser.Term.argument| $x:term)
  | `(doc_arg|+$x) =>
    `(Parser.Term.argument| ($x := true))
  | `(doc_arg|-$x) =>
    `(Parser.Term.argument| ($x := false))
  | `(doc_arg|($x := $v)) =>
    let v ← mkArgVal v
    `(Parser.Term.argument| ($x := $v))
  | `(doc_arg|$x:ident := $v) =>
    logWarningAt arg "Obsolete syntax" -- TODO suggestion
    let v ← mkArgVal v
    `(Parser.Term.argument| ($x := $v))
  | _ => throwErrorAt arg "Didn't understand as argument"

private def mkAppStx (name : Ident) (args : TSyntaxArray `doc_arg) : DocM Term := do
  return ⟨mkNode ``Parser.Term.app #[name, mkNullNode (← args.mapM mkArg)]⟩

/--
If `true`, suggestions are provided for code elements.
-/
register_builtin_option doc.verso.suggestions : Bool := {
  defValue := true
  descr := "whether to provide suggestions for code elements"
  group := "doc"
}

-- Normally, name suggestions should be provided relative to the current scope. But
-- during bootstrapping, the names in question may not yet be defined, so builtin
-- names need special handling.
private def suggestionName (name : Name) : TermElabM Name := do
  let name' ←
    -- Builtin expander names never need namespacing
    if (← builtinDocRoles.get).contains name then pure (some name)
    else if (← builtinDocCodeBlocks.get).contains name then pure (some name)
    else pure none
  match name' with
    | some (.str _ s) => return .str .anonymous s
    | some n => return n
    | none =>
      -- If it exists, unresolve it
      if (← getEnv).contains name then
        unresolveNameGlobalAvoidingLocals name
      else
        -- Fall back to doing nothing
        pure name

private def sortSuggestions (ss : Array Meta.Hint.Suggestion) : Array Meta.Hint.Suggestion :=
  let cmp : (x y : Meta.Tactic.TryThis.SuggestionText) → Bool
    | .string s1, .string s2 => s1 < s2
    | .string _, _ => true
    | .tsyntax _, .string _ => false
    | .tsyntax s1, .tsyntax s2 => toString s1.raw < toString s2.raw
  ss.qsort (cmp ·.suggestion ·.suggestion)

open Diff in
private def mkSuggestion
    (ref : Syntax) (hintTitle : MessageData)
    (newStrings : Array (String × Option String × Option String)) :
    DocM MessageData := do
  match (← read).suggestionMode with
  | .interactive =>
    hintTitle.hint (newStrings.map fun (s, preInfo?, postInfo?) => { suggestion := s, preInfo?, postInfo? }) (ref? := some ref)
  | .batch =>
    let some ⟨b, e⟩ := ref.getRange?
      | pure m!""
    let text ← getFileMap
    let pre := text.source.extract 0 b
    let post := text.source.extract e text.source.endPos
    let edits := newStrings.map fun (s, _, _) =>
      let lines := text.source.split (· == '\n') |>.toArray
      let s' := pre ++ s ++ post
      let lines' := s'.split (· == '\n') |>.toArray
      let d := diff lines lines'
      toMessageData <| Diff.linesToString <| d.filter (·.1 != Action.skip)
    pure m!"\n\nHint: {hintTitle}\n{indentD <| m!"\n".joinSep edits.toList}"

def nameOrBuiltinName [Monad m] [MonadEnv m] (x : Name) : m Name := do
  let env ← getEnv
  if env.contains x then return x
  else return `Lean.Doc ++ x

/--
Elaborates the syntax of an inline document element to an actual inline document element.
-/
public partial def elabInline (stx : TSyntax `inline) : DocM (Inline ElabInline) :=
  withRef stx <|
  withInfoContext (mkInfo := pure <| .ofDocInfo {elaborator := decl_name%, stx := stx}) do
  match stx with
  | `(inline|$s:str) =>
    return .text s.getString
  | `(inline|_[$inl*]) =>
    return .emph (← inl.mapM elabInline)
  | `(inline|*[$inl*]) =>
    return .bold (← inl.mapM elabInline)
  | `(inline|link[$inl*]($url)) =>
    return .link (← inl.mapM elabInline) url.getString
  | `(inline|link[$inl*][$name]) =>
    return .other (delayLink name) (← inl.mapM elabInline)
  | `(inline|image($alt)($url)) =>
    -- TODO forward ref to URL
    return .image alt.getString url.getString
  | `(inline|image($alt)[$name]) =>
    return .other (delayImage alt.getString name) #[]
  | `(inline|footnote($ref)) =>
    return .other (delayFootnote ref) #[]
  | `(inline|line!$s) =>
    return .linebreak s.getString
  | `(inline|code($s)) =>
    if doc.verso.suggestions.get (← getOptions) then
      if let some ⟨b, e⟩ := stx.raw.getRange? then
        let suggesters ← codeSuggestions
        let mut suggestions := #[]
        for suggest in suggesters do
          try suggestions := suggestions ++ (← withEnableInfoTree false <| suggest s)
          catch | _ => pure ()
        unless suggestions.isEmpty do
          let text ← getFileMap
          let str := text.source.extract b e
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
          let litSuggestion :=
            ( "{lit}" ++ str,
              some "Use the `lit` role:\n",
              some "\nto mark the code as literal text and disable suggestions" )
          let ss := ss.push litSuggestion
          let hint ← mkSuggestion stx m!"Insert a role to document it:" ss
          logWarning m!"Code element could be more specific.{hint}"
    return .code s.getString
  | `(inline|\math code($s)) =>
    return .math .inline s.getString
  | `(inline|\displaymath code($s)) =>
    return .math .display s.getString
  | `(inline|role{$name $args*}[$inl*]) =>
    let expanders ← roleExpandersFor name
    for (exName, ex) in expanders do
      try
        let res ← ex inl args <&> (·.1)
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
    throwErrorAt name "Unkown role `{name}`"
  | other =>
    throwErrorAt other "Unsupported syntax {other}"
where
  withSpace (s : String) : String :=
    if s.startsWith " " then s else " " ++ s

/--
Elaborates the syntax of an block-level document element to an actual block-level document element.
-/
public partial def elabBlock (stx : TSyntax `block) : DocM (Block ElabInline ElabBlock) :=
  withRef stx <|
  withInfoContext (mkInfo := pure <| .ofDocInfo {elaborator := decl_name%, stx := stx}) do
  match stx with
  | `(block|para[$inls*]) =>
    .para <$> inls.mapM elabInline
  | `(block|ul{$[* $itemss*]*}) =>
    .ul <$> itemss.mapM fun items =>
      .mk <$> items.mapM elabBlock
  | `(block|ol($n){$[* $itemss*]*}) =>
    .ol n.getNat <$> itemss.mapM fun items =>
      .mk <$> items.mapM elabBlock
  | `(block|dl{$items*}) =>
    .dl <$> items.mapM fun itemStx =>
      withRef itemStx do
      match itemStx with
      | `(desc_item|: $term* => $desc*) =>
        return .mk (← term.mapM elabInline) (← desc.mapM elabBlock)
      | _ => throwUnsupportedSyntax
  | `(block|[^$ref]: $content*) =>
    let refStr := ref.getString
    if (← getThe InternalState).footnotes.contains refStr then
      throwErrorAt ref m!"Reference already found"
    else
      let content ← content.mapM elabInline
      modifyThe InternalState fun st =>
        { st with
          footnotes := st.footnotes.insert refStr { content := .concat content, location := ref } }
    return .empty
  | `(block|[$ref]: $url) =>
    let refStr := ref.getString
    if (← getThe InternalState).urls.contains refStr then
      throwErrorAt ref m!"Reference already found"
    else
      modifyThe InternalState fun st =>
        { st with
          urls := st.urls.insert refStr { content := url.getString, location := ref } }
    return .empty
  | `(block| ::: $name $args* { $content*}) =>
    let expanders ← directiveExpandersFor name
    for (exName, ex) in expanders do
      try
        let res ← ex content args <&> (·.1)
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
    throwErrorAt name "Unknown directive `{name}`"
  | `(block| ```%$opener | $s ```) =>
    if doc.verso.suggestions.get (← getOptions) then
      if let some ⟨b, e⟩ := opener.getRange? then
        let suggesters ← codeBlockSuggestions
        let mut suggestions := #[]
        for suggest in suggesters do
          try suggestions := suggestions ++ (← withEnableInfoTree false <| suggest s)
          catch | _ => pure ()
        unless suggestions.isEmpty do
          let text ← getFileMap
          let str := text.source.extract b e
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
  | `(block| ```$name $args* | $s ```) =>
    let expanders ← codeBlockExpandersFor name
    for (exName, ex) in expanders do
      try
        let res ← ex s args <&> (·.1)
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
    throwErrorAt name "Unknown code block `{name}`"
  | `(block| command{$name $args*}) =>
    let expanders ← commandExpandersFor name
    for (exName, ex) in expanders do
      try
        let res ← ex args <&> (·.1)
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
    throwErrorAt name "Unknown document command `{name}`"
  | `(block|%%%$_*%%%) =>
    let h ←
      if stx.raw.getRange?.isSome then m!"Remove it".hint #[""] (ref? := stx)
      else pure m!""
    logError m!"Part metadata is not supported in docstrings.{h}"
    return .empty
  | other => throwErrorAt other "Unsupported syntax: {other}"
where
  withSpace (s : String) : String :=
    if s.endsWith " " then s else s ++ " "

private def takeFirst? (xs : Array α) : Option (α × Array α) :=
  if h : xs.size > 0 then
    some (xs[0], xs.extract 1)
  else none

private partial def elabBlocks' (level : Nat) :
    StateT (TSyntaxArray `block) DocM (Array (Block ElabInline ElabBlock) × Array (Part ElabInline ElabBlock Empty)) := do
  let mut pre := #[]
  let mut sub := #[]
  repeat
    if let some (x, xs) := takeFirst? (← getThe (TSyntaxArray `block)) then
      if let `(block|header($n){$name*}) := x then
        let n := n.getNat
        if n < level then return (pre, sub)
        else if n = level then
          set xs
          let (content, subParts) ← elabBlocks' (level + 1)
          let title ←
            liftM <| withInfoContext (mkInfo := pure <| .ofDocInfo {elaborator := `no_elab, stx := x}) <|
              name.mapM elabInline
          let mdTitle := ToMarkdown.toMarkdown (Inline.concat title) |>.run'
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

private def elabModSnippet'
    (range : DeclarationRange) (level : Nat) (blocks : TSyntaxArray `block) :
    DocM VersoModuleDocs.Snippet := do
  let mut snippet : VersoModuleDocs.Snippet := {
    declarationRange := range
  }
  let mut maxLevel := level
  for b in blocks do
    if let `(block|header($n){$name*}) := b then
        let n := n.getNat
        if n > maxLevel then
          logErrorAt b m!"Incorrect header nesting: expected at most `{"#".pushn '#' maxLevel}` \
            but got `{"#".pushn '#' n}`"
        else
          let title ←
            liftM <| withInfoContext (mkInfo := pure <| .ofDocInfo {elaborator := `no_elab, stx := b}) <|
              name.mapM elabInline
          let some headerRange ← getDeclarationRange? b
            | throwErrorAt b "Can't find header source position"
          let mdTitle := ToMarkdown.toMarkdown (Inline.concat title) |>.run'
          snippet := snippet.addPart n headerRange {
            title,
            titleString := mdTitle
            metadata := none, content := #[], subParts := #[]
          }
      else
        snippet := snippet.addBlock (← elabBlock b)
  return snippet

private partial def fixupInline (inl : Inline ElabInline) : DocM (Inline ElabInline) := do
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
  | .other i@{ name, val } xs =>
    match name with
    | ``delayLink =>
      let some {name} := val.get? ElabLink
        | throwError "Wrong value for {name}: {val.typeName}"
      let nameStr := name.getString
      if let some r@{content := url, seen, .. } := (← getThe InternalState).urls[nameStr]? then
        unless seen do modifyThe InternalState fun st => { st with urls := st.urls.insert nameStr { r with seen := true } }
        return .link (← xs.mapM fixupInline) url
      else
        logErrorAt name "Reference not found"
        return .concat (← xs.mapM fixupInline)
    | ``delayImage =>
      let some {alt, name} := val.get? ElabImage
        | throwError "Wrong value for {name}: {val.typeName}"
      let nameStr := name.getString
      if let some r@{content := url, seen, ..} := (← getThe InternalState).urls[nameStr]? then
        unless seen do modifyThe InternalState fun st => { st with urls := st.urls.insert nameStr { r with seen := true } }
        return .image alt url
      else
        logErrorAt name "Reference not found"
        return .empty
    | ``delayFootnote =>
      let some {name} := val.get? ElabFootnote
        | throwError "Wrong value for {name}: {val.typeName}"
      let nameStr := name.getString
      if let some r@{content, seen, ..} := (← getThe InternalState).footnotes[nameStr]? then
        unless seen do modifyThe InternalState fun st =>
          { st with footnotes := st.footnotes.insert nameStr { r with seen := true } }
        return .footnote nameStr #[← fixupInline content]
      else
        logErrorAt name "Footnote not found"
        return .empty
    | _ => .other i <$> xs.mapM fixupInline

private partial def fixupBlock (block : Block ElabInline ElabBlock) : DocM (Block ElabInline ElabBlock) := do
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

private partial def fixupPart (part : Part ElabInline ElabBlock Empty) : DocM (Part ElabInline ElabBlock Empty) := do
  return { part with
    title := ← part.title.mapM fixupInline
    content := ← part.content.mapM fixupBlock,
    subParts := ← part.subParts.mapM fixupPart
  }


private partial def fixupBlocks : (Array (Block ElabInline ElabBlock) × Array (Part ElabInline ElabBlock Empty)) → DocM (Array (Block ElabInline ElabBlock) × Array (Part ElabInline ElabBlock Empty))
  | (bs, ps) => do
    let bs ← bs.mapM fixupBlock
    let ps ← ps.mapM fixupPart
    return (bs, ps)

private partial def fixupSnippet (snippet : VersoModuleDocs.Snippet) : DocM VersoModuleDocs.Snippet := do
  return {snippet with
    text := ← snippet.text.mapM fixupBlock,
    sections := ← snippet.sections.mapM fun (level, range, content) => do
      return (level, range, ← fixupPart content)
  }
/--
After fixing up the references, check to see which were not used and emit a suitable warning.
-/
private def warnUnusedRefs : DocM Unit := do
  for (_, {location, seen, ..}) in (← getThe InternalState).urls do
    unless seen do
      logWarningAt location "Unused URL"
  for (_, {location, seen, ..}) in (← getThe InternalState).footnotes do
    unless seen do
      logWarningAt location "Unused footnote"

/-- Elaborates a sequence of blocks into a document. -/
public def elabBlocks (blocks : TSyntaxArray `block) :
    DocM (Array (Block ElabInline ElabBlock) × Array (Part ElabInline ElabBlock Empty)) := do
  -- Users should not need to make import needed for embedded terms public
  withoutExporting do
    let (v, _) ← elabBlocks' 0 |>.run blocks
    let res ← fixupBlocks v
    warnUnusedRefs
    return res

/-- Elaborates a sequence of blocks into a module doc snippet. -/
public def elabModSnippet
    (range : DeclarationRange) (blocks : TSyntaxArray `block) (nestingLevel : Nat) :
    DocM (VersoModuleDocs.Snippet) := do
  let s ← elabModSnippet' range nestingLevel blocks
  let s ← fixupSnippet s
  warnUnusedRefs
  return s
