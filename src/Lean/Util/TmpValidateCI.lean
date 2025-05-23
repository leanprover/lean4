import Lean

import Std.Internal.Parsec

-- FIXME: all the `return false`s need to undo the change to the stack...

open Lean Meta

inductive ErrorExplanationCodeInfo.Kind
  | broken | fixed
deriving Repr, Inhabited, BEq

instance : ToString ErrorExplanationCodeInfo.Kind where
  toString
  | .broken => "broken"
  | .fixed => "fixed"

structure ErrorExplanationCodeInfo where
  lang : String
  kind? : Option ErrorExplanationCodeInfo.Kind
  title? : Option String
deriving Repr

namespace ErrorExplanationCodeInfo
open Std.Internal Parsec Parsec.String

namespace Parse

def word : Parser String := fun it =>
  -- TODO: allow escaping
  let it' := it.find fun c => c == '"'
  .success it' (it.extract it')

def languageName : Parser String := fun it =>
  let it' := it.find fun c => !c.isAlphanum
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

def infoString : Parser ErrorExplanationCodeInfo := do
  let lang ← languageName
  let attrs ← Parsec.many (ws *> attr)
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

def parse (s : String) : Except String ErrorExplanationCodeInfo :=
  Parse.infoString.run s |>.mapError (fun s => s!"Invalid code block info string: {s}")

end ErrorExplanationCodeInfo

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

def manyD (p : ValidationM α) : ValidationM Unit :=
  discard (many p)

-- A hack to let us show errors other than "not EOF"
partial def manyDThenEOF (p : ValidationM α) : ValidationM Unit := fun s =>
  match p s with
  | .success s' _ => manyDThenEOF p s'
  | .error s' err =>
    match eof s' with
    | .success s'' _ => .success s'' ()
    | .error s'' _ => .error s'' err

def optionalD (p : ValidationM α) : ValidationM Unit :=
  discard (optional p)

def atLeastOneD (p : ValidationM α) : ValidationM Unit :=
  p *> manyD p

def notD (p : ValidationM α) : ValidationM Unit :=
  notFollowedBy p *> skip

def parseExplanation : ValidationM Unit := do
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

  codeBlock (lang : String) (kind? : Option ErrorExplanationCodeInfo.Kind := none) := attempt do
    let infoString ← fence
      <|> fail s!"Expected a(n){kind?.map (s!" {·}") |>.getD ""} `{lang}` code block"
    manyD (notD fence)
    let closing ← fence
      <|> fail s!"Missing closing code fence for block with header '{infoString}'"
    -- Validate parsed code block:
    let info ← match ErrorExplanationCodeInfo.parse infoString with
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

def validateExplanation (explanation : String) :=
  parseExplanation.run explanation

#eval IO.ofExcept <| validateExplanation "# Examples
## Foo
```lean broken
```
```output
```
```lean fixed
```

## Bar
```lean broken
```
"

#eval IO.ofExcept <| validateExplanation "# Examples
# End of Examples"

#eval IO.ofExcept <| validateExplanation "# Examples
## Example
```lean fixed
```
```output
```
```lean broken
```
"
#eval IO.ofExcept <| validateExplanation "\
This is a bunch

of explanation.

```lean
def canIncludeCode := true
```

# Examples

## My first example

```lean broken
```

```output
```

```lean fixed
```

## My second example

```lean broken
```

```output
```

```lean fixed
this should not fail
```

# Something New

Foo
"

#eval IO.ofExcept <| validateExplanation "
# Examples
## Test Last Line
```lean broken
```
```output
```
```lean fixed
```
"


#eval IO.ofExcept <| validateExplanation "
This is some text

And this is some more

# Examples ... Not

## Here's not an example

```lean
def foo := 32
```

# Something Else

Hi!

# Examples

## My Example

```lean broken
```

```output
```

```lean fixed (title := \"Foo\")
```

Here's an explanation of what's up!

"

  -- Structure:
  -- 1. General description
  -- 2. # Examples [note: 2 may not be present, in which case there should be no 3s]
  -- 3(a). ## Example name
  -- 3(b). ```lean broken (title := "title")? ```
  -- 3(c). ```output ```
  -- 3(d)(i). ```lean fixed (title := "title")? ```
  -- 3(d)(ii). (optional) ```output ```
  -- 3(d)*
  -- 3(e). Example description
  -- 3* [note: we can also legally have no 3s at all]
  -- 4. (optional) # Any other header
  -- 5. (optional) General description
  -- Additional check: all code blocks that aren't `broken` should be error free

def main : IO UInt32 := do
  unsafe withImportModules #[`Lean.Util.ErrorExplanation] {} fun env => do
    let expls := Lean.getErrorExplanationsRaw env
    for (_, expl) in expls do
      try
        IO.ofExcept <| validateErrorExplanation expl.doc
      catch e =>
        IO.eprintln e
        return 1
    return 0
