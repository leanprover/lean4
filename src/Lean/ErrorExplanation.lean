/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Rotella
-/
prelude

import Lean.Message
import Lean.EnvExtension
import Lean.DocString.Links

namespace Lean

/--
Metadata for an error explanation.

* `summary` gives a short description of the error
* `sinceVersion` indicates the version of Lean in which an error with this error name was introduced
* `severity` is the severity of the diagnostic
* `removedVersion` indicates the version of Lean in which this error name was retired, if applicable
-/
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

/--
The kind of a code block in an error explanation example. `broken` blocks raise the diagnostic being
explained; `fixed` blocks must compile successfully.
-/
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

/-- Metadata about a code block in an error explanation, parsed from the block's info string. -/
structure CodeInfo where
  lang : String
  kind? : Option CodeInfo.Kind
  title? : Option String
deriving Repr

open Std.Internal Parsec Parsec.String in
/-- Parse metadata for an error explanation code block from its info string. -/
def CodeInfo.parse (s : String) : Except String CodeInfo :=
  infoString.run s |>.mapError (fun e => s!"Invalid code block info string `{s}`: {e}")
where
  /-- Parses the contents of a string literal up to, but excluding, the closing quotation mark. -/
  stringContents : Parser String := attempt do
    let escaped := pchar '\\' *> pchar '"'
    let cs ← many (notFollowedBy (pchar '"') *> (escaped <|> any))
    return String.mk cs.toList

  /--
  Parses all input up to the next whitespace. If `nonempty` is `true`, fails if there is no input
  prior to the next whitespace.
  -/
  upToWs (nonempty : Bool) : Parser String := fun it =>
    let it' := it.find fun c => c.isWhitespace
    if nonempty && it'.pos == it.pos then
      .error it' "Expected a nonempty string"
    else
      .success it' (it.extract it')

  /-- Parses a named attribute, and returns its name and value. -/
  namedAttr : Parser (String × String) := attempt do
    let name ← skipChar '(' *> ws *> (upToWs true)
    let contents ← ws *> skipString ":=" *> ws *> skipChar '"' *> stringContents
    discard <| skipChar '"' *> ws *> skipChar ')'
    return (name, contents)

  /--
  Parses an "attribute" in an info string, either a space-delineated identifier or a named
  attribute of the form `(name := "value")`.
  -/
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
            fail "Redundant title specifications"
        else
          fail s!"Invalid named attribute `{name}`; expected `title`"
    return { lang, title?, kind? }

open Std.Internal Parsec

/--
An iterator storing nonempty lines in an error explanation together with their original line
numbers.
-/
private structure ValidationState where
  lines : Array (String × Nat)
  idx   : Nat := 0
deriving Repr, Inhabited

/-- Creates an iterator for validation from the raw contents of an error explanation. -/
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
  if _ : s.lines.size = 0 then
    0
  else
    s.lines[min s.idx (s.lines.size - 1)].2

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
private partial def manyThenEOF (p : ValidationM α) : ValidationM Unit := fun s =>
  match eof s with
  | .success .. => .success s ()
  | .error .. =>
    match p s with
    | .success s' _ => manyThenEOF p s'
    | .error s' err => .error s' err

/-- Repeatedly parses the next input as long as it satisfies `p`, and discards the result. -/
private partial def manyD (p : ValidationM α) : ValidationM Unit :=
  Parsec.tryCatch p (fun _ => manyD p) (fun _ => pure ())

/-- Parses one or more inputs as long as they satisfy `p`, and discards the result. -/
private def many1D (p : ValidationM α) : ValidationM Unit :=
  p *> manyD p

/-- Repeatedly parses the next input as long as it fails to satisfy `p`, and discards the result. -/
private def manyNotD (p : ValidationM α) : ValidationM Unit :=
  manyD (notFollowedBy p *> skip)

/-- Parses an error explanation: a general description followed by an examples section. -/
private def parseExplanation : ValidationM Unit := do
  manyNotD examplesHeader
  eof <|> (examplesHeader *> manyThenEOF singleExample)
where
  /-- The top-level `# Examples` header -/
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
      many1D (codeBlock "output")
      many1D do
        let leanBlock ← codeBlock "lean" (some .fixed)
        let outputBlocks ← many (codeBlock "output")
        return (leanBlock, outputBlocks)
      manyNotD exampleEndingHeader

  /-- A level-2 header for a single example. -/
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
    manyD (notFollowedBy (fence numTicks) *> any)
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

  /-- Prepends an error raised by `x` to indicate that it arose in example `header`. -/
  labelingExampleErrors {α} (header : String) (x : ValidationM α) : ValidationM α := fun s =>
    match x s with
    | res@(.success ..) => res
    | .error s' msg => .error s' s!"Example '{header}' is malformed: {msg}"

  /--
  If `line` is a level-`level` header and, if `title?` is non-`none`, its title is `title?`,
  then returns the contents of the header at `line` (i.e., stripping the leading `#`). Returns
  `none` if `line` is not a header of the appropriate form.
  -/
  matchHeader (level : Nat) (title? : Option String) (line : String) : Option String := do
    let octsEndPos := line.nextWhile (· == '#') 0
    guard (octsEndPos.byteIdx == level)
    guard (line.get octsEndPos == ' ')
    let titleStartPos := line.next octsEndPos
    let title := Substring.mk line titleStartPos line.endPos |>.toString
    let titleMatches : Bool := match title? with
      | some expectedTitle => title == expectedTitle
      | none => true
    guard titleMatches
    some title

/--
Validates that the given error explanation has the expected structure. If an error is found, it is
represented as a pair `(lineNumber, errorMessage)` where `lineNumber` gives the 0-based offset from
the first line of `doc` at which the error occurs.
-/
def processDoc (doc : String) : Except (Nat × String) Unit :=
  parseExplanation.run doc

end ErrorExplanation

/-- An environment extension that stores error explanations.  -/
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

In general, use `Lean.getErrorExplanation?` instead if the body of the explanation will be used.
-/
def getErrorExplanationRaw? (env : Environment) (name : Name) : Option ErrorExplanation := do
  errorExplanationExt.getState env |>.find? name

/-- Returns `true` if there exists an error explanation named `name`. -/
def hasErrorExplanation [Monad m] [MonadEnv m] [MonadLiftT BaseIO m] (name : Name) : m Bool :=
  return errorExplanationExt.getState (← getEnv) |>.contains name

/--
Returns all error explanations with their names as an unsorted array, *without* rewriting manual
links.

In general, use `Lean.getErrorExplanations` or `Lean.getErrorExplanationsSorted` instead of this
function if the bodies of the fetched explanations will be used.
-/
def getErrorExplanationsRaw (env : Environment) : Array (Name × ErrorExplanation) :=
  errorExplanationExt.getState env |>.toArray

/-- Returns all error explanations with their names, rewriting manual links. -/
def getErrorExplanations [Monad m] [MonadEnv m] [MonadLiftT BaseIO m] : m (Array (Name × ErrorExplanation)) := do
  let entries := errorExplanationExt.getState (← getEnv) |>.toArray
  entries
    |>.mapM fun (n, e) => return (n, { e with doc := (← rewriteManualLinks e.doc) })

/--
Returns all error explanations with their names as a sorted array, rewriting manual links.
-/
def getErrorExplanationsSorted [Monad m] [MonadEnv m] [MonadLiftT BaseIO m] : m (Array (Name × ErrorExplanation)) := do
  return (← getErrorExplanations).qsort fun e e' => e.1.toString < e'.1.toString

end Lean
