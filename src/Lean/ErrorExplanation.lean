prelude

import Lean.Meta.Eval
import Lean.Elab.Term
import Lean.Elab.Command
import Lean.Widget.UserWidget
import Std.Internal.Parsec

namespace Lean

-- We cannot import the definitions needed for this attribute in `Lean.Log`, so we instead add it
-- here
attribute [builtin_widget_module] Lean.errorDescriptionWidget

structure ErrorExplanation.Metadata where
  summary : String
  sinceVersion : String
  severity : MessageSeverity     := .error
  removedVersion : Option String := none
deriving FromJson, ToJson

structure ErrorExplanation.CodeBlockSet where
  broken : String
  brokenOutputs : Array String
  fixedWithOutputs : Array (String × Array String)
  deriving Repr

structure ErrorExplanation where
  doc : String
  codeBlocks : Array ErrorExplanation.CodeBlockSet
  metadata : ErrorExplanation.Metadata

-- FIXME: `addImportedFn`
initialize errorExplanationExt : SimplePersistentEnvExtension (Name × ErrorExplanation) (NameMap ErrorExplanation) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun s (n, v) => s.insert n v
    addImportedFn := fun entries => RBMap.ofList entries.flatten.toList
  }

/--
Gets an error explanation for the given name if one exists, rewriting manual links.
-/
def getErrorExplanation? [Monad m] [MonadEnv m] [MonadLiftT BaseIO m] (name : Name) : m (Option ErrorExplanation) :=
  do
  let explan? := errorExplanationExt.getState (← getEnv) |>.find? name
  explan?.mapM fun explan =>
    return { explan with doc := (← rewriteManualLinks explan.doc) }

/-- Returns true if there exists an error explanation named `name`. -/
def hasErrorExplanation [Monad m] [MonadEnv m] [MonadLiftT BaseIO m] (name : Name) : m Bool :=
  return errorExplanationExt.getState (← getEnv) |>.contains name

/--
Returns all error explanations with their names as an unsorted array, *without* rewriting manual
links.

In general, one should use `Lean.getErrorExplanationsSorted` instead of this function. This function
is primarily intended for internal use during CI.
-/
def getErrorExplanationsRaw (env : Environment) : Array (Name × ErrorExplanation) :=
  errorExplanationExt.getState env |>.toArray

private partial def compareNamedExplanations (ne ne' : Name × ErrorExplanation) : Ordering :=
  match ne.2.metadata.removedVersion, ne'.2.metadata.removedVersion with
  | .none, .none | .some _, .some _ => compare ne.1.toString ne'.1.toString
  | .none, .some _ => .lt
  | .some _, .none => .gt

/--
Returns all error explanations with their names as a sorted array, rewriting manual links.
-/
def getErrorExplanationsSorted [Monad m] [MonadEnv m] [MonadLiftT BaseIO m] : m (Array (Name × ErrorExplanation)) := do
  let entries := errorExplanationExt.getState (← getEnv) |>.toArray
  entries
    |>.qsort (fun e e' => (compareNamedExplanations e e').isLT)
    |>.mapM fun (n, e) => return (n, { e with doc := (← rewriteManualLinks e.doc) })

namespace ErrorExplanation

inductive CodeInfo.Kind
  | broken | fixed
deriving Repr, Inhabited, BEq

instance : ToString CodeInfo.Kind where
  toString
  | .broken => "broken"
  | .fixed => "fixed"

def CodeInfo.Kind.ofString : String → Option CodeInfo.Kind
  | "broken" => some .broken
  | "fixed" => some .fixed
  | _ => none

structure CodeInfo where
  lang : String
  kind? : Option CodeInfo.Kind
  title? : Option String
deriving Repr

open Std.Internal Parsec Parsec.String in
def CodeInfo.parse (s : String) : Except String CodeInfo :=
  infoString.run s |>.mapError (fun e => s!"Invalid code block info string `{s}`: {e}")
where
  stringContents : Parser String := attempt do
    let escaped := pchar '\\' *> pchar '"'
    let cs ← many (notFollowedBy (pchar '"') *> (escaped <|> any))
    return String.mk cs.toList

  upToWs (nonempty : Bool) : Parser String := fun it =>
    let it' := it.find fun c => c.isWhitespace
    if nonempty && it'.pos == it.pos then
      .error it' "Expected a nonempty string"
    else
      .success it' (it.extract it')

  namedAttr : Parser (String × String) := attempt do
    let name ← skipChar '(' *> ws *> (upToWs true)
    let contents ← ws *> skipString ":=" *> ws *> skipChar '"' *> stringContents
    discard <| skipChar '"' *> ws *> skipChar ')'
    return (name, contents)

  attr : Parser (String ⊕ String × String) :=
    .inr <$> namedAttr <|> .inl <$> (upToWs true)

  infoString : Parser CodeInfo := do
    let lang ← (upToWs false)
    let attrs ← many (attempt <| ws *> attr)
    let mut kind? := Option.none
    let mut title? := Option.none
    for attr in attrs do
      match attr with
      | .inl atomicAttr =>
        match atomicAttr with
        | "broken" | "fixed" =>
          match kind? with
          | none => kind? := Kind.ofString atomicAttr
          | some kind =>
            fail s!"redundant kind specifications: previously `{kind}`; now `{atomicAttr}`"
        | _ => fail s!"invalid attribute {atomicAttr}"
      | .inr (name, val) =>
        if name == "title" then
          if title?.isNone then
            title? := some val
          else
            fail "redundant name specifications"
        else
          fail s!"Invalid named attribute `{name}`"
    return { lang, title?, kind? }

open Std.Internal Parsec

def matchHeader (level : Nat) (title? : Option String) (line : String) : Option String :=
  let init := line.take (level + 1)
  let expected := ⟨List.replicate level '#'⟩ ++ " "
  let initMatches := init == expected
  let actual := line.drop (level + 1)
  let titleMatches? := title?.map fun title =>
    actual == title
  if initMatches && titleMatches?.getD true then
    some actual
  else
    none

private structure ValidationState where
  lines : Array (String × Nat)
  idx   : Nat := 0
deriving Repr, Inhabited

private def ValidationState.ofSource (input : String) : ValidationState where
  lines := input.splitOn "\n"
    |>.zipIdx
    |>.filter (!·.1.trim.isEmpty)
    |>.toArray

-- Workaround to account for the fact that `Input` expects "EOF" to be a valid position
private def ValidationState.get (s : ValidationState) :=
  if _ : s.idx < s.lines.size then
    s.lines[s.idx].1
  else
    ""

private def ValidationState.getLineNumber (s : ValidationState) :=
  s.lines[min s.idx (s.lines.size - 1)]!.2

instance : Input ValidationState String Nat where
  pos := ValidationState.idx
  next := fun s => { s with idx := min (s.idx + 1) s.lines.size }
  curr := ValidationState.get
  hasNext := fun s => s.idx < s.lines.size
  next' := fun s _ => { s with idx := s.idx + 1 }
  curr' := fun s _ => s.get

abbrev ValidationM := Parsec ValidationState

def ValidationM.run (p : ValidationM α) (input : String) : Except (Nat × String) α :=
  match p (.ofSource input) with
  | .success _ res => Except.ok res
  | .error s err  => Except.error (s.getLineNumber, err)

-- A hack to let us show errors other than "not EOF"
private partial def manyThenEOF (p : ValidationM α) : ValidationM (Array α) :=
  go #[]
where
  go (acc : Array α) := fun s =>
    match p s with
    | .success s' x => go (acc.push x) s'
    | .error s' err =>
      match eof s' with
      | .success s'' _ => .success s'' acc
      | .error _ _ => .error s' err

private def manyNotD (p : ValidationM α) : ValidationM Unit :=
  discard (many (notFollowedBy p *> skip))

private def parseExplanation : ValidationM (Array ErrorExplanation.CodeBlockSet) := do
  manyNotD examplesHeader
  (eof *> pure #[]) <|> (examplesHeader *> manyThenEOF singleExample)
where
  examplesHeader := attempt do
    let line ← any
    if (matchHeader 1 "Examples" line).isSome then
      return
    else
      fail s!"Expected level-1 'Examples' header, but found `{line}`"

  singleExample := attempt do
    let header ← exampleHeader
    labelingExampleErrors header do
      let broken ← codeBlock "lean" (some .broken)
      let brokenOutputs ← many1 (codeBlock "output")
      let fixedWithOutputs ← many1 do
        let leanBlock ← codeBlock "lean" (some .fixed)
        let outputBlocks ← many (codeBlock "output")
        return (leanBlock, outputBlocks)
      manyNotD exampleEndingHeader
      return { broken, brokenOutputs, fixedWithOutputs : ErrorExplanation.CodeBlockSet }

  exampleHeader := attempt do
    let line ← any
    if let some header := matchHeader 2 none line then
      return header
    else
      fail s!"Expected level-2 header for an example section, but found `{line}`"

  /-- A header capable of ending an example. -/
  exampleEndingHeader := attempt do
    let line ← any
    if (matchHeader 1 none line).isSome || (matchHeader 2 none line).isSome then
      return
    else
      fail s!"Expected a level-1 or level-2 header, but found `{line}`"

  nonExamplesL1Header : ValidationM Unit := attempt do
    let line ← any
    match matchHeader 1 none line with
    | some "Examples" =>
      fail s!"Duplicate 'Examples' header; each explanation can have at most one 'Examples' section"
    | some _ => pure ()
    | none => fail s!"Expected a level-1 header, but found '{line}'"

  codeBlock (lang : String) (kind? : Option ErrorExplanation.CodeInfo.Kind := none) := attempt do
    let infoString ← fence
      <|> fail s!"Expected a(n){kind?.map (s!" {·}") |>.getD ""} `{lang}` code block"
    let code ← many (notFollowedBy fence *> any)
    let closing ← fence
      <|> fail s!"Missing closing code fence for block with header '{infoString}'"
    -- Validate parsed code block:
    let info ← match ErrorExplanation.CodeInfo.parse infoString with
      | .ok i => pure i
      | .error s =>
        fail s
    let langMatches := info.lang == lang
    let kindMatches := (kind?.map (some · == info.kind?)).getD true
    unless langMatches && kindMatches do
      let (expKind, actKind) := match kind? with
        | some kind =>
          let actualKindStr := (info.kind?.map (s!" {·}")).getD " unspecified-kind"
          (s!" {kind}", actualKindStr)
        | none => ("", "")
      fail s!"Expected a(n){expKind} `{lang}` code block, but found a(n){actKind} `{info.lang}` one"
    unless closing.trim.isEmpty do
      fail s!"Expected a closing code fence, but found the nonempty info string `{closing}`"
    return "\n".intercalate code.toList

  fence := attempt do
    let line ← any
    if line.startsWith "```" then
      return line.drop 3
    else
      -- Don't put `line` in backticks here because it might be a partial code fence
      fail s!"Expected a code fence, but found:\n{line}"

  labelingExampleErrors {α} (header : String) (x : ValidationM α) : ValidationM α := fun s =>
    match x s with
    | res@(.success ..) => res
    | .error s msg => .error s s!"Example '{header}' is malformed: {msg}"

/--
Validates that the given error explanation has the expected structure, and extracts its code blocks.
-/
def processDoc (doc : String) :=
  parseExplanation.run doc

end ErrorExplanation

-- TODO: create a helper function `msg name ↦ .tagged (tagForError name) msg`
protected def throwNamedError [Monad m] [MonadError m] (name : Name) (msg : MessageData) : m α := do
  let ref ← getRef
  let msg := .tagged (tagForError name) msg
  let (ref, msg) ← AddErrorMessageContext.add ref msg
  throw <| Exception.error ref msg

protected def throwNamedErrorAt [Monad m] [MonadError m] (ref : Syntax) (name : Name) (msg : MessageData) : m α := do
  withRef ref <| Lean.throwNamedError name msg

section
variable [Monad m] [MonadLog m] [AddMessageContext m] [MonadOptions m]
/-- Log a new error message using the given message data. The position is provided by `getRef`. -/
def logNamedError (name : Name) (msgData : MessageData) : m Unit :=
  log (.tagged (tagForError name) msgData) MessageSeverity.error

/-- Log a new error message using the given message data. The position is provided by `ref`. -/
protected def logNamedErrorAt (ref : Syntax) (name : Name) (msgData : MessageData) : m Unit :=
  logAt ref (.tagged (tagForError name) msgData) MessageSeverity.error
end

-- TODO: the following QoL features would be very helpful (i > ii -- probably i >> ii):
-- (i) cmd-click on error names to jump to the explanation   <-- Could labeled sorries be a model?
-- (ii) autocomplete with registered error explanation names
syntax (name := throwNamedErrorStx) "throwNamedError " ident ppSpace (interpolatedStr(term) <|> term) : term
syntax (name := throwNamedErrorAtStx) "throwNamedErrorAt " term:max ppSpace ident ppSpace (interpolatedStr(term) <|> term) : term
syntax (name := logNamedErrorStx) "logNamedError " ident ppSpace (interpolatedStr(term) <|> term) : term
syntax (name := logNamedErrorAtStx) "logNamedErrorAt " term:max ppSpace ident ppSpace (interpolatedStr(term) <|> term) : term

def expandThrowNamedError : Macro
  | `(throwNamedError $id $msg:interpolatedStr) => ``(Lean.throwNamedError $(quote id.getId) m! $msg)
  | `(throwNamedError $id $msg:term) => ``(Lean.throwNamedError $(quote id.getId) $msg)
  | `(throwNamedErrorAt $ref $id $msg:interpolatedStr) => ``(Lean.throwNamedErrorAt $ref $(quote id.getId) m! $msg)
  | `(throwNamedErrorAt $ref $id $msg:term) => ``(Lean.throwNamedErrorAt $ref $(quote id.getId) $msg)
  | `(logNamedError $id $msg:interpolatedStr) => ``(Lean.logError $(quote id.getId) m! $msg)
  | `(logNamedError $id $msg:term) => ``(Lean.logNamedError $(quote id.getId) $msg)
  | `(logNamedErrorAt $ref $id $msg:interpolatedStr) => ``(Lean.logNamedErrorAt $ref $(quote id.getId) m! $msg)
  | `(logNamedErrorAt $ref $id $msg:term) => ``(Lean.logNamedErrorAt $ref $(quote id.getId) $msg)
  | _ => Macro.throwUnsupported

open Lean Elab Term in
@[builtin_term_elab throwNamedErrorStx, builtin_term_elab throwNamedErrorAtStx,
  builtin_term_elab logNamedErrorStx, builtin_term_elab logNamedErrorAtStx]
def elabCheckedNamedError : TermElab
  | stx@`(throwNamedError $id $_msg), expType?
  | stx@`(throwNamedErrorAt $_ref $id $_msg), expType?
  | stx@`(logNamedError $id $_msg), expType?
  | stx@`(logNamedErrorAt $_ref $id $_msg), expType? => do
    let name := id.getId
    unless (← hasErrorExplanation name) do
      throwError m!"There is no explanation associated with the name `{name}`. \
        Add an explanation of this error to the `Lean.ErrorExplanation` module."
    let stx' ← liftMacroM <| expandThrowNamedError stx
    elabTerm stx' expType?
  | _, _ => throwUnsupportedSyntax

open Elab Meta Term Command in
/--
Registers an error explanation.

Note that the provided name is not relativized to the current namespace.
-/
elab docStx:docComment cmd:"register_error_explanation " nm:ident t:term : command => withRef cmd do
  let tp := mkConst ``ErrorExplanation.Metadata []
  let metadata ← runTermElabM <| fun _ => unsafe do
    let e ← elabTerm t tp
    if e.hasSyntheticSorry then throwAbortTerm
    evalExpr ErrorExplanation.Metadata tp e
  let name := nm.getId
  if name.isAnonymous then throwErrorAt nm "Invalid name for error explanation: `{nm}`"
  validateDocComment docStx
  let doc ← getDocStringText docStx
  if errorExplanationExt.getState (← getEnv) |>.contains name then
    throwErrorAt nm m!"Cannot add explanation: An error explanation already exists for `{name}`"
  let codeBlocks ←
    match ErrorExplanation.processDoc doc with
    | .ok bs => pure bs
    | .error (lineOffset, msg) =>
      let some range := docStx.raw[1].getRange? | throwError msg
      let fileMap ← getFileMap
      let ⟨startLine, _⟩ := fileMap.toPosition range.start
      let errLine := startLine + lineOffset
      let synth := Syntax.ofRange { start := fileMap.ofPosition ⟨errLine, 0⟩,
                                    stop  := fileMap.ofPosition ⟨errLine + 1, 0⟩ }
      throwErrorAt synth msg
  modifyEnv (errorExplanationExt.addEntry · (name, { metadata, doc, codeBlocks }))

end Lean
