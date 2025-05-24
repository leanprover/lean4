import Lean

import Std.Internal.Parsec

open Lean Meta

-- inductive ErrorExplanationCodeInfo.Kind
--   | broken | fixed
-- deriving Repr, Inhabited, BEq

-- instance : ToString ErrorExplanationCodeInfo.Kind where
--   toString
--   | .broken => "broken"
--   | .fixed => "fixed"

-- structure ErrorExplanationCodeInfo where
--   lang : String
--   kind? : Option ErrorExplanationCodeInfo.Kind
--   title? : Option String
-- deriving Repr

-- namespace ErrorExplanationCodeInfo
-- open Std.Internal Parsec Parsec.String

-- namespace Parse

-- def word : Parser String := fun it =>
--   -- TODO: allow escaping
--   let it' := it.find fun c => c == '"'
--   .success it' (it.extract it')

-- def languageName : Parser String := fun it =>
--   let it' := it.find fun c => !c.isAlphanum
--   .success it' (it.extract it')

-- def snippetKind : Parser Kind := do
--   (pstring "broken" *> pure .broken)
--   <|> (pstring "fixed" *> pure .fixed)

-- def title : Parser String :=
--   skipChar '(' *> optional ws *> skipString "title" *> ws *> skipString ":=" *> ws *> skipChar '"' *>
--   word
--   <* skipChar '"' <* optional ws <* skipChar ')'

-- def attr : Parser (Kind ⊕ String) :=
--   .inl <$> snippetKind <|> .inr <$> title

-- def infoString : Parser ErrorExplanationCodeInfo := do
--   let lang ← languageName
--   let attrs ← Parsec.many (ws *> attr)
--   let mut kind? := Option.none
--   let mut title? := Option.none
--   for attr in attrs do
--     match attr with
--     | .inl k =>
--       if kind?.isNone then
--         kind? := some k
--       else
--         Parsec.fail "redundant kind specifications"
--     | .inr n =>
--       if title?.isNone then
--         title? := some n
--       else
--         Parsec.fail "redundant name specifications"
--   return { lang, title?, kind? }

-- end Parse

-- def parse (s : String) : Except String ErrorExplanationCodeInfo :=
--   Parse.infoString.run s |>.mapError (fun s => s!"Invalid code block info string: {s}")

-- end ErrorExplanationCodeInfo

open ErrorExplanation

/-- error: (9, Example 'Bar' is malformed: Expected a(n) `output` code block) -/
#guard_msgs in
#eval IO.ofExcept <| processDoc "# Examples
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

/-- error: (1, Expected level-2 header for an example section, but found `# End of Examples`) -/
#guard_msgs in
#eval IO.ofExcept <| processDoc "# Examples
# End of Examples"

/--
error: (1, Example 'Example' is malformed: Expected a(n) broken `lean` code block, but found a(n) fixed `lean` one)
-/
#guard_msgs in
#eval IO.ofExcept <| processDoc "# Examples
## Example
```lean fixed
```
```output
```
```lean broken
```
"

#eval IO.ofExcept <| processDoc "This is an explanation.

# Examples
## Ex

```lean broken
thing 1
```
```output
output
```
```lean fixed
this is fixed
```

# Examples

Should fail"

#eval IO.ofExcept <| processDoc "\
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

#eval IO.ofExcept <| processDoc "
# Examples
## Test Last Line
```lean broken
```
```output
```
```lean fixed
```
"


#eval IO.ofExcept <| processDoc "
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

Here's an explanation!

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

-- def main : IO UInt32 := do
--   unsafe withImportModules #[`Lean.Util.ErrorExplanation] {} fun env => do
--     let expls := Lean.getErrorExplanationsRaw env
--     for (_, expl) in expls do
--       try
--         IO.ofExcept <| validateErrorExplanation expl.doc
--       catch e =>
--         IO.eprintln e
--         return 1
--     return 0

/--
This is a great explanation.

# Examples
## Ex

```lean broken
thing 1
```
```output
output
```
```lean fixed
this works
```
-/
register_error_explanation Foo {
  summary := "Hello"
  sinceVersion := "4.0.0"
}


/--
error: Example 'Hi!' is malformed: Expected a(n) `output` code block, but found a(n) `lean` one
-/
#guard_msgs in
/--
Foo

# Examples
## Hi!
```lean broken
```
```lean fixed
```
-/
register_error_explanation Foo2 {
  summary := "hi"
  sinceVersion := "4.0.0"
}
