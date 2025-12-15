/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Rotella
-/
module

prelude

public import Lean.Message
public import Lean.EnvExtension
public import Lean.DocString.Links
import Init.Data.String.TakeDrop
import Init.Data.String.Extra
import Init.Data.String.Search

public section

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
  removedVersion? : Option String := none
  deriving FromJson, ToJson

/--
An explanation of a named error message.

Error explanations are rendered in the manual; a link to the resulting manual page is displayed at
the bottom of corresponding error messages thrown using `throwNamedError` or `throwNamedErrorAt`.
-/
structure ErrorExplanation where
  metadata : ErrorExplanation.Metadata
  declLoc? : Option DeclarationLocation

namespace ErrorExplanation

/--
Returns the error explanation summary prepended with its severity. For use in completions and
hovers.
-/
def summaryWithSeverity (explan : ErrorExplanation) : String :=
  s!"({explan.metadata.severity}) {explan.metadata.summary}"

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
    return String.ofList cs.toList

  /--
  Parses all input up to the next whitespace. If `nonempty` is `true`, fails if there is no input
  prior to the next whitespace.
  -/
  upToWs (nonempty : Bool) : Parser String := fun it =>
    let it' := (it.2.find? fun (c : Char) => c.isWhitespace).getD it.1.endPos
    if nonempty && it' == it.2 then
      .error ⟨_, it'⟩ (.other "Expected a nonempty string")
    else
      .success ⟨_, it'⟩ (it.1.slice! it.2 it').copy

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
  lines := input.split '\n'
    |>.filter (!·.trimAscii.isEmpty)
    |>.toStringArray
    |>.zipIdx

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
  | .error s err  => Except.error (s.getLineNumber, toString err)



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
  return errorExplanationExt.getState (← getEnv) |>.find? name

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
  return errorExplanationExt.getState (← getEnv) |>.toArray

/--
Returns all error explanations with their names as a sorted array, rewriting manual links.
-/
def getErrorExplanationsSorted [Monad m] [MonadEnv m] [MonadLiftT BaseIO m] : m (Array (Name × ErrorExplanation)) := do
  return (← getErrorExplanations).qsort fun e e' => e.1.toString < e'.1.toString

end Lean
