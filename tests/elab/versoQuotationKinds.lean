import Lean

/-!
An element written in a quotation of its own kind is the same syntax as the element written in a
quotation of its category, so nothing is lost by building an element at its kind and coercing it.
-/

open Lean Doc Parser Elab Command

/-- Reports the elements for which coercion is not identical to parsing. -/
def report (what : String) (elements : Array (String × Syntax × Syntax)) : CommandElabM Unit := do
  let mut bad := #[]
  for (name, own, category) in elements do
    unless own == category do bad := bad.push (name, own, category)
  if bad.isEmpty then
    IO.println s!"{what}: all {elements.size} agree"
  else
    IO.println s!"{what}: {bad.size} of {elements.size} differ"
    for (name, own, category) in bad do
      IO.println s!"  {name}\n    own kind: {own}\n    category: {category}"

/-- Reports the inline elements for which coercion is not identical to parsing. -/
def reportInlines
    (elements : Array (String × TSyntax ``Parser.inline × TSyntax ``Parser.inline)) :
    CommandElabM Unit :=
  report "inline" (elements.map fun (name, own, category) => (name, own.raw, category.raw))

/-- Reports the block elements for which coercion is not identical to parsing. -/
def reportBlocks
    (elements : Array (String × TSyntax ``Parser.block × TSyntax ``Parser.block)) :
    CommandElabM Unit :=
  report "block" (elements.map fun (name, own, category) => (name, own.raw, category.raw))

/--
info: inline: all 11 agree
-/
#guard_msgs in
#eval show CommandElabM Unit from do
  let text ← mkVersoTextFromRef "t"
  let content : TSyntaxArray ``Parser.inline := #[← `(Parser.inline| $text:versoText)]
  let code ← mkVersoCodeFromRef "x"
  let alt ← mkVersoImageAltFromRef "a"
  let url ← mkVersoLinkUrlFromRef "u"
  let name ← mkVersoRefNameFromRef "n"
  let role := mkIdent `role
  let linebreak ← mkVersoLinebreakFromRef
  reportInlines #[
    ("text",
      ← `(Parser.Inline.text| $text:versoText),
      ← `(Parser.inline| $text:versoText)),
    ("emph",
      ← `(Parser.Inline.emph| _$[$content]*_),
      ← `(Parser.inline| _$[$content]*_)),
    ("bold",
      ← `(Parser.Inline.bold| *$[$content]**),
      ← `(Parser.inline| *$[$content]**)),
    ("code",
      ← `(Parser.Inline.code| `$code`),
      ← `(Parser.inline| `$code`)),
    ("inline_math",
      ← `(Parser.Inline.inline_math| $`$code`),
      ← `(Parser.inline| $`$code`)),
    ("display_math",
      ← `(Parser.Inline.display_math| $$`$code`),
      ← `(Parser.inline| $$`$code`)),
    ("link",
      ← `(Parser.Inline.link| [$[$content]*]($url)),
      ← `(Parser.inline| [$[$content]*]($url))),
    ("image",
      ← `(Parser.Inline.image| ![$alt]($url)),
      ← `(Parser.inline| ![$alt]($url))),
    ("footnote",
      ← `(Parser.Inline.footnote| [^$name]),
      ← `(Parser.inline| [^$name])),
    -- A line break is written as the newline it stands for, which a quotation reads as whitespace,
    -- so it is built rather than written.
    ("linebreak",
      linebreak,
      ← `(Parser.inline| $linebreak)),
    ("role",
      ← `(Parser.Inline.role| {$role}[$[$content]*]),
      ← `(Parser.inline| {$role}[$[$content]*]))]

/--
info: block: all 12 agree
-/
#guard_msgs in
#eval show CommandElabM Unit from do
  let text ← mkVersoTextFromRef "t"
  let content : TSyntaxArray ``Parser.inline := #[← `(Parser.inline| $text:versoText)]
  let blocks : TSyntaxArray ``Parser.block := #[← `(Parser.block| $[$content]*)]
  let codeBlock ← mkVersoCodeBlockFromRef "x"
  let name ← mkVersoRefNameFromRef "n"
  let url ← mkVersoLinkRefUrlFromRef "u"
  let command := mkIdent `command
  let directive := mkIdent `directive
  reportBlocks #[
    ("para",
      ← `(Parser.Block.para| $[$content]*),
      ← `(Parser.block| $[$content]*)),
    ("ul",
      ← `(Parser.Block.ul| * $[$blocks]*),
      ← `(Parser.block| * $[$blocks]*)),
    ("ol",
      ← `(Parser.Block.ol| 1. $[$blocks]*),
      ← `(Parser.block| 1. $[$blocks]*)),
    ("dl",
      ← `(Parser.Block.dl| : $[$content]*),
      ← `(Parser.block| : $[$content]*)),
    ("blockquote",
      ← `(Parser.Block.blockquote| > $[$blocks]*),
      ← `(Parser.block| > $[$blocks]*)),
    ("codeblock",
      ← `(Parser.Block.codeblock| ```$codeBlock:versoCodeBlock```),
      ← `(Parser.block| ```$codeBlock:versoCodeBlock```)),
    ("directive",
      ← `(Parser.Block.directive| :::$directive # $[$content]* :::),
      ← `(Parser.block| :::$directive # $[$content]* :::)),
    ("header",
      ← `(Parser.Block.header| # $[$content]*),
      ← `(Parser.block| # $[$content]*)),
    ("link_ref",
      ← `(Parser.Block.link_ref| [$name]: $url),
      ← `(Parser.block| [$name]: $url)),
    ("footnote_ref",
      ← `(Parser.Block.footnote_ref| [^$name]: $[$content]*),
      ← `(Parser.block| [^$name]: $[$content]*)),
    ("metadata_block",
      ← `(Parser.Block.metadata_block| %%%field := 1%%%),
      ← `(Parser.block| %%%field := 1%%%)),
    ("command",
      ← `(Parser.Block.command| {$command}),
      ← `(Parser.block| {$command}))]
