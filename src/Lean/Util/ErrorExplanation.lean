prelude

import Lean.Meta.Eval
import Lean.Elab.Term
import Lean.Elab.Command
import Std.Internal.Parsec

-- TODO: ensure this all still works

namespace Lean

structure ErrorExplanation.Metadata where
  summary : String
  sinceVersion : String
  severity : MessageSeverity     := .error
  removedVersion : Option String := none
deriving FromJson, ToJson

structure ErrorExplanation where
  doc : String
  metadata : ErrorExplanation.Metadata

-- FIXME: `addImportedFn`
initialize errorExplanationExt : SimplePersistentEnvExtension (Name × ErrorExplanation) (NameMap ErrorExplanation) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun s (n, v) => s.insert n v
    addImportedFn := fun entries => RBMap.ofList entries.flatten.toList
  }
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
  if name.isAnonymous then throwErrorAt nm "Invalid name for error explanation: '{nm}'"
  validateDocComment docStx
  let doc ← getDocStringText docStx
  if errorExplanationExt.getState (← getEnv) |>.contains name then
    throwError m!"Cannot add explanation: An error explanation already exists for '{name}'"
  modifyEnv (errorExplanationExt.addEntry · (name, { metadata, doc }))

/--
Gets an error explanation for the given name if one exists, rewriting manual links.
-/
def getErrorExplanation? [Monad m] [MonadEnv m] [MonadLiftT BaseIO m] (name : Name) : m (Option ErrorExplanation) :=
  do
  let explan? := errorExplanationExt.getState (← getEnv) |>.find? name
  explan?.mapM fun explan =>
    return { explan with doc := (← rewriteManualLinks explan.doc) }

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

structure CodeInfo where
  lang : String
  kind? : Option CodeInfo.Kind
  title? : Option String
deriving Repr

namespace CodeInfo
open Std.Internal Parsec Parsec.String

namespace Parse

def word : Parser String := attempt do
  let escaped := pchar '\\' *> pchar '"'
  let cs ← many (notFollowedBy (pchar '"') *> (escaped <|> any))
  return String.mk cs.toList

def languageName : Parser String := fun it =>
  let it' := it.find fun c => c.isWhitespace
  .success it' (it.extract it')

def snippetKind : Parser Kind := do
  (pstring "broken" *> pure .broken)
  <|> (pstring "fixed" *> pure .fixed)

def title : Parser String :=
  skipChar '(' *> optional ws *> skipString "title" *> ws *> skipString ":=" *> ws *> skipChar '"' *>
  word
  <* skipChar '"' <* optional ws <* skipChar ')'

def attr : Parser (Kind ⊕ String) :=
  .inl <$> snippetKind <|> .inr <$> title

def infoString : Parser CodeInfo := do
  let lang ← languageName
  let attrs ← Parsec.many (attempt <| ws *> attr)
  let mut kind? := Option.none
  let mut title? := Option.none
  for attr in attrs do
    match attr with
    | .inl k =>
      if kind?.isNone then
        kind? := some k
      else
        Parsec.fail "redundant kind specifications"
    | .inr n =>
      if title?.isNone then
        title? := some n
      else
        Parsec.fail "redundant name specifications"
  return { lang, title?, kind? }

end Parse

def parse (s : String) : Except String CodeInfo :=
  Parse.infoString.run s |>.mapError (fun s => s!"Invalid code block info string: {s}")

end CodeInfo

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

structure ValidationState where
  lines : Array (String × Nat)
  idx   : Nat := 0
deriving Repr

def ValidationState.ofSource (input : String) : ValidationState where
  lines := input.splitOn "\n"
    |>.zipIdx
    |>.filter (!·.1.trim.isEmpty)
    |>.toArray

-- Workaround to account for the fact that `Input` expects "EOF" to be a valid position
def ValidationState.get (s : ValidationState) :=
  if _ : s.idx < s.lines.size then
    s.lines[s.idx].1
  else
    ""

def ValidationState.getLineNumber (s : ValidationState) :=
  s.lines[min s.idx (s.lines.size - 1)]!.2 + 1

instance : Input ValidationState String Nat where
  pos := ValidationState.idx
  next := fun s => { s with idx := min (s.idx + 1) s.lines.size }
  curr := ValidationState.get
  hasNext := fun s => s.idx < s.lines.size
  next' := fun s _ => { s with idx := s.idx + 1 }
  curr' := fun s _ => s.get

abbrev ValidationM := Parsec ValidationState

def ValidationM.run (p : ValidationM α) (input : String) : Except String α :=
  match p (.ofSource input) with
  | .success _ res => Except.ok res
  | .error s err  => Except.error s!"Line {s.getLineNumber}: {err}"

private def manyD (p : ValidationM α) : ValidationM Unit :=
  discard (many p)

-- A hack to let us show errors other than "not EOF". `manyDThenEOF p` is equivalent (on accepted
-- inputs) to `manyD p *> eof`.
private partial def manyDThenEOF (p : ValidationM α) : ValidationM Unit := fun s =>
  match p s with
  | .success s' _ => manyDThenEOF p s'
  | .error s' err =>
    match eof s' with
    | .success s'' _ => .success s'' ()
    | .error s'' _ => .error s'' err

private def optionalD (p : ValidationM α) : ValidationM Unit :=
  discard (optional p)

private def atLeastOneD (p : ValidationM α) : ValidationM Unit :=
  p *> manyD p

private def notD (p : ValidationM α) : ValidationM Unit :=
  notFollowedBy p *> skip

private def parseExplanation : ValidationM Unit := do
  manyD (notD examplesHeader)
  eof <|> optionalD do
    examplesHeader
    -- This is really `manyD (...) *> eof`
    manyDThenEOF (singleExample *> optionalD (level1Header *> manyD (notD examplesHeader)))
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
      codeBlock "lean" (some .broken)
      atLeastOneD (codeBlock "output")
      atLeastOneD (codeBlock "lean" (some .fixed) *> manyD (codeBlock "output"))
      manyD (notD exampleEndingHeader)

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

  -- TODO: clean these up
  level1Header : ValidationM Unit := attempt do
    let line ← any
    unless (matchHeader 1 none line).isSome do
      fail s!"Expected a level-1 header, but found '{line}'"

  codeBlock (lang : String) (kind? : Option CodeInfo.Kind := none) := attempt do
    let infoString ← fence
      <|> fail s!"Expected a(n){kind?.map (s!" {·}") |>.getD ""} `{lang}` code block"
    manyD (notD fence)
    let closing ← fence
      <|> fail s!"Missing closing code fence for block with header '{infoString}'"
    -- Validate parsed code block:
    let info ← match CodeInfo.parse infoString with
      | .ok i => pure i
      | .error s => fail s!"Invalid info string `{infoString}` on code block: {s}"
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

def validateDoc (explanation : String) :=
  parseExplanation.run explanation

end ErrorExplanation

end Lean
