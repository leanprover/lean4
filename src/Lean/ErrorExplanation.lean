prelude

import Lean.Message
import Lean.EnvExtension
import Lean.DocString.Links

namespace Lean

/-- Metadata for an error explanation. -/
structure ErrorExplanation.Metadata where
  summary : String
  sinceVersion : String
  severity : MessageSeverity     := .error
  removedVersion : Option String := none
  deriving FromJson, ToJson

/--
Describes the location where (the identifier for) an error explanation is declared.

We want to avoid polluting the environment with dummy declarations for error explanations (since,
outside of the manual, we care only about their names), but we still want jump-to-location
functionality to work; we use these location values to facilitate that.
-/
structure ErrorExplanation.Location where
  uri        : String
  rangeStart : Nat × Nat
  rangeEnd   : Nat × Nat

/--
An explanation of a named error message.

Error explanations are rendered in the manual; a link to the resulting manual page is displayed at
the bottom of corresponding error messages thrown using `throwNamedError` or `throwNamedErrorAt`.
-/
structure ErrorExplanation where
  doc : String
  metadata : ErrorExplanation.Metadata
  declLoc? : Option ErrorExplanation.Location

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
    let lang ← upToWs false
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
            fail s!"Redundant kind specifications: previously `{kind}`; now `{atomicAttr}`"
        | _ => fail s!"Invalid attribute `{atomicAttr}`"
      | .inr (name, val) =>
        if name == "title" then
          if title?.isNone then
            title? := some val
          else
            fail "Redundant name specifications"
        else
          fail s!"Invalid named attribute `{name}`"
    return { lang, title?, kind? }

open Std.Internal Parsec

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

private instance : Input ValidationState String Nat where
  pos := ValidationState.idx
  next := fun s => { s with idx := min (s.idx + 1) s.lines.size }
  curr := ValidationState.get
  hasNext := fun s => s.idx < s.lines.size
  next' := fun s _ => { s with idx := s.idx + 1 }
  curr' := fun s _ => s.get

private abbrev ValidationM := Parsec ValidationState

private def ValidationM.run (p : ValidationM α) (input : String) : Except (Nat × String) α :=
  match p (.ofSource input) with
  | .success _ res => Except.ok res
  | .error s err  => Except.error (s.getLineNumber, err)

/--
Matches `p` as many times as possible, followed by EOF. If `p` cannot be matched prior to the end
of the input, rethrows the corresponding error.
-/
private partial def manyThenEOF (p : ValidationM α) : ValidationM (Array α) :=
  loop #[]
where
  loop (acc : Array α) := fun s =>
    match eof s with
    | .success .. => .success s acc
    | .error .. =>
      match p s with
      | .success s' x => loop (acc.push x) s'
      | .error s' err => .error s' err

private def manyNotD (p : ValidationM α) : ValidationM Unit :=
  discard (many (notFollowedBy p *> skip))

private def parseExplanation : ValidationM Unit := do
  manyNotD examplesHeader
  eof <|> (examplesHeader *> discard (manyThenEOF singleExample))
where
  examplesHeader := attempt do
    let line ← any
    if (matchHeader 1 "Examples" line).isSome then
      return
    else
      fail s!"Expected level-1 'Examples' header, but found `{line}`"

  -- We needn't `attempt` examples because they never appear in a location where backtracking is
  -- possible, and persisting the line index allows better error message placement
  singleExample := do
    let header ← exampleHeader
    labelingExampleErrors header do
      codeBlock "lean" (some .broken)
      discard <| many1 (codeBlock "output")
      discard <| many1 do
        let leanBlock ← codeBlock "lean" (some .fixed)
        let outputBlocks ← many (codeBlock "output")
        return (leanBlock, outputBlocks)
      manyNotD exampleEndingHeader

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

  codeBlock (lang : String) (kind? : Option ErrorExplanation.CodeInfo.Kind := none) := attempt do
    let (numTicks, infoString) ← fence
      <|> fail s!"Expected a(n){kind?.map (s!" {·}") |>.getD ""} `{lang}` code block"
    discard <| many (notFollowedBy (fence numTicks) *> any)
    let (_, closing) ← fence numTicks
      <|> fail s!"Missing closing code fence for block with header '{infoString}'"
    -- Validate code block:
    unless closing.trim.isEmpty do
      fail s!"Expected a closing code fence, but found the nonempty info string `{closing}`"
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

  fence (ticksToClose : Option Nat := none) := attempt do
    let line ← any
    if line.startsWith "```" then
      let numTicks := line.takeWhile (· == '`') |>.length
      match ticksToClose with
      | none => return (numTicks, line.drop numTicks)
      | some n =>
        if numTicks == n then
          return (numTicks, line.drop numTicks)
        else
          fail s!"Expected a closing code fence with {n} ticks, but found:\n{line}"
    else
      -- Don't put `line` in backticks here because it might be a partial code fence
      fail s!"Expected a code fence, but found:\n{line}"

  labelingExampleErrors {α} (header : String) (x : ValidationM α) : ValidationM α := fun s =>
    match x s with
    | res@(.success ..) => res
    | .error s' msg => .error s' s!"Example '{header}' is malformed: {msg}"

  matchHeader (level : Nat) (title? : Option String) (line : String) : Option String :=
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

/--
Validates that the given error explanation has the expected structure, and extracts its code blocks.
-/
def processDoc (doc : String) :=
  parseExplanation.run doc

end ErrorExplanation

builtin_initialize errorExplanationExt : SimplePersistentEnvExtension (Name × ErrorExplanation) (NameMap ErrorExplanation) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun s (n, v) => s.insert n v
    addImportedFn := fun ess =>
      ess.foldl (init := ∅) fun acc es =>
        es.foldl (init := acc) fun acc (n, v) =>
          acc.insert n v
  }

/-- Returns an error explanation for the given name if one exists, rewriting manual links. -/
def getErrorExplanation? [Monad m] [MonadEnv m] [MonadLiftT BaseIO m] (name : Name) : m (Option ErrorExplanation) := do
  let explan? := errorExplanationExt.getState (← getEnv) |>.find? name
  explan?.mapM fun explan =>
    return { explan with doc := (← rewriteManualLinks explan.doc) }

/--
Returns an error explanation for the given name if one exists *without* rewriting manual links.

In general, `getErrorExplanation?` should be used if the body of the explanation will be accessed.
-/
def getErrorExplanationRaw? (env : Environment) (name : Name) : Option ErrorExplanation := do
  errorExplanationExt.getState env |>.find? name

/-- Returns true if there exists an error explanation named `name`. -/
def hasErrorExplanation [Monad m] [MonadEnv m] [MonadLiftT BaseIO m] (name : Name) : m Bool :=
  return errorExplanationExt.getState (← getEnv) |>.contains name

/--
Returns all error explanations with their names as an unsorted array, *without* rewriting manual
links.

In general, one should use `Lean.getErrorExplanations` or `Lean.getErrorExplanationsSorted` instead
of this function. This function is primarily intended for internal use.
-/
def getErrorExplanationsRaw (env : Environment) : Array (Name × ErrorExplanation) :=
  errorExplanationExt.getState env |>.toArray

/-- Returns all error explanations with their names, rewriting manual links. -/
def getErrorExplanations [Monad m] [MonadEnv m] [MonadLiftT BaseIO m] : m (Array (Name × ErrorExplanation)) := do
  let entries := errorExplanationExt.getState (← getEnv) |>.toArray
  entries
    |>.mapM fun (n, e) => return (n, { e with doc := (← rewriteManualLinks e.doc) })

private partial def compareNamedExplanations (ne ne' : Name × ErrorExplanation) : Ordering :=
  match ne.2.metadata.removedVersion, ne'.2.metadata.removedVersion with
  | .none, .none | .some _, .some _ => compare ne.1.toString ne'.1.toString
  | .none, .some _ => .lt
  | .some _, .none => .gt

/--
Returns all error explanations with their names as a sorted array, rewriting manual links.
-/
def getErrorExplanationsSorted [Monad m] [MonadEnv m] [MonadLiftT BaseIO m] : m (Array (Name × ErrorExplanation)) := do
  return (← getErrorExplanations).qsort fun e e' => (compareNamedExplanations e e').isLT

end Lean
