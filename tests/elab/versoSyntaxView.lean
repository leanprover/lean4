import Lean

/-!
Tests the view layer for Verso document concrete syntax (`Lean.Doc.InlineView`,
`Lean.Doc.BlockView`, and friends). The tests take views of parser output and of syntax that
quotations construct, and render the resulting shapes compactly. A view presents the parser's
encoding, so a quotation's syntax renders as the parser's atoms, delimiters, and list markers.
-/

open Lean Doc Parser

def describeTarget : LinkTargetView → String
  | .url _ o u c => s!"url({u.getVersoLinkUrl.quote})[{o.getAtomVal}|{c.getAtomVal}]"
  | .ref _ o n c => s!"ref({n.getVersoRefName.quote})[{o.getAtomVal}|{c.getAtomVal}]"

def describeArgVal (stx : TSyntax ``Parser.argVal) : String :=
  match ArgValView.of stx with
  | none => s!"ERR-argVal({stx.raw.getKind})"
  | some (.str _ val) => s!"str({val.quote})"
  | some (.name x) => s!"name({x.getId.eraseMacroScopes})"
  | some (.num _ val) => s!"num({val})"

def describeArg (stx : TSyntax ``Parser.arg) : String :=
  match ArgView.of stx with
  | none => s!"ERR-arg({stx.raw.getKind})"
  | some (.anon _ v) => s!"anon({describeArgVal v})"
  | some (.named _ parens x _ v) =>
    s!"named({x.getId.eraseMacroScopes}:={describeArgVal v}{if parens.isSome then ", parens" else ""})"
  | some (.flag _ sign x isOn) => s!"flag({sign.getAtomVal}{x.getId.eraseMacroScopes}, {isOn})"

def describeArgs (args : TSyntaxArray ``Parser.arg) : String :=
  " ".intercalate (args.toList.map describeArg)

partial def describeInline (stx : TSyntax ``Parser.inline) : String :=
  match InlineView.of stx with
  | none => s!"ERR-inline({stx.raw.getKind})"
  | some v =>
    match v with
    | .text v => s!"text({v.getVersoText.quote})"
    | .emph v =>
      s!"emph[{v.opener.getVersoDelimiter}|{describeAll v.content}|{v.closer.getVersoDelimiter}]"
    | .bold v =>
      s!"bold[{v.opener.getVersoDelimiter}|{describeAll v.content}|{v.closer.getVersoDelimiter}]"
    | .code v => s!"code[{describeCode v}]"
    | .math v =>
      s!"math({if v.mode == .inline then "inline" else "display"})[{v.marker.getVersoDelimiter}|{describeCode v.code}]"
    | .link v =>
      s!"link[{v.opener.getAtomVal}|{describeAll v.content}|{v.closer.getAtomVal}|{describeTarget v.target}]"
    | .image v =>
      s!"image({v.getAlt.quote})[{v.opener.getAtomVal}|{v.closer.getAtomVal}|{describeTarget v.target}]"
    | .footnote v =>
      s!"footnote({v.getName.quote})[{v.opener.getAtomVal}|{v.closer.getAtomVal}]"
    | .linebreak v => s!"linebreak({v.newline.getAtomVal.quote})"
    | .role v =>
      let bs :=
        match v.brackets with
        | some (o, c) => s!"{o.getAtomVal}{c.getAtomVal}"
        | none => "bare"
      s!"role({v.name.getId.eraseMacroScopes})({describeArgs v.args})[{v.braceOpen.getAtomVal}{v.braceClose.getAtomVal}{bs}|{describeAll v.content}]"
where
  describeAll (content : TSyntaxArray ``Parser.inline) : String :=
    " ".intercalate (content.toList.map (describeInline ·))
  describeCode (v : CodeView) : String :=
    s!"{v.opener.getVersoDelimiter}|{v.getVersoCode.quote}|{v.closer.getVersoDelimiter}"

partial def describeBlock (stx : TSyntax ``Parser.block) : String :=
  match BlockView.of stx with
  | none => s!"ERR-block({stx.raw.getKind})"
  | some v =>
    match v with
    | .para v => s!"para[{inlines v.content}]"
    | .ul v => s!"ul[{" ".intercalate (v.items.toList.map unorderedItem)}]"
    | .ol v => s!"ol({v.start})[{" ".intercalate (v.items.toList.map orderedItem)}]"
    | .dl v => s!"dl[{" ".intercalate (v.items.toList.map descItem)}]"
    | .blockquote v => s!"quote({v.marker.getAtomVal})[{blocks v.content}]"
    | .codeblock v =>
      s!"codeblock({v.name?.map (·.getId.eraseMacroScopes) |>.getD .anonymous})({describeArgs v.args})[{v.openFence.getVersoDelimiter}|{v.getVersoCodeBlock.quote}|{v.closeFence.getVersoDelimiter}]"
    | .directive v =>
      s!"directive({v.name.getId.eraseMacroScopes})({describeArgs v.args})[{v.opener.getVersoDelimiter}|{blocks v.content}|{v.closer.getVersoDelimiter}]"
    | .command v =>
      s!"command({v.name.getId.eraseMacroScopes})({describeArgs v.args})[{v.braceOpen.getAtomVal}|{v.braceClose.getAtomVal}]"
    | .header v =>
      s!"header({v.level})[{v.marker.getVersoDelimiter}|{inlines v.content}]"
    | .linkRef v =>
      s!"linkRef({v.getName.quote}:={v.getUrl.quote})[{v.opener.getAtomVal}|{v.closer.getAtomVal}]"
    | .footnoteRef v =>
      s!"footnoteRef({v.getName.quote})[{v.opener.getAtomVal}|{v.closer.getAtomVal}|{inlines v.content}]"
    | .metadata v =>
      s!"metadata(n={v.fields.size})[{v.opener.getAtomVal}|{v.closer.getAtomVal}]"
where
  inlines (content : TSyntaxArray ``Parser.inline) : String :=
    " ".intercalate (content.toList.map (describeInline ·))
  blocks (content : TSyntaxArray ``Parser.block) : String :=
    " ".intercalate (content.toList.map (describeBlock ·))
  unorderedItem (i : UnorderedListItemView) : String :=
    s!"item({i.marker.getVersoDelimiter})[{blocks i.contents}]"
  orderedItem (i : OrderedListItemView) : String :=
    s!"item({i.marker.getVersoDelimiter})[{blocks i.contents}]"
  descItem (i : DescItemView) : String :=
    s!"desc({i.marker.getAtomVal})[{inlines i.term}|{blocks i.desc}]"

/-- Parses `input` as a Verso document and describes the view of each block. -/
def checkParsed (input : String) : IO Unit := do
  let ictx := mkInputContext input "<input>"
  let env : Environment ← mkEmptyEnvironment
  let pmctx : ParserModuleContext := {env := env, options := {}}
  let s := (documentFn).run ictx pmctx (getTokenTable env) (mkParserState input)
  unless s.allErrors.isEmpty do
    throw <| IO.userError s!"parse errors in {input.quote}"
  let doc : VersoDocument := ⟨s.stxStack.back⟩
  for b in doc.getVersoBlocks do
    IO.println (describeBlock ⟨b⟩)

/--
info: para[text("Hello ") bold[*|text("world")|*] text(" and ") emph[_|text("also")|_] text(" ") code[``|"co`de"|``] text(" ") math(inline)[$|`|"x+1"|`] text(" ") math(display)[$$|`|"y"|`] text("!")]
-/
#guard_msgs in
#eval checkParsed "Hello *world* and _also_ ``co`de`` $`x+1` $$`y`!"

/--
info: para[text("A ") link[[|text("link ") bold[*|text("text")|*]|]|url("https://example.com")[(|)]] text(" or ") link[[|text("ref")|]|ref("named")[[|]]] text(" or ") image("alt text")[![|]|url("img.png")[(|)]] text(" or ") footnote("fn")[[^|]] text(".")]
-/
#guard_msgs in
#eval checkParsed
  "A [link *text*](https://example.com) or [ref][named] or ![alt text](img.png) or [^fn]."

/--
info: para[role(role)(named(arg:=str("val"), parens) flag(+flag, true) anon(name(positional)))[{}[]|text("content ") bold[*|text("here")|*]]]
para[role(lit)()[{}bare|code[`|"bracketless"|`]]]
-/
#guard_msgs in
#eval checkParsed
  "{role (arg := \"val\") +flag positional}[content *here*]\n\n{lit}`bracketless`"

/--
info: header(0)[#|text("Header one")]
para[text("some text") linebreak("\n") text("next line")]
-/
#guard_msgs in
#eval checkParsed "# Header one\n\nsome text\nnext line"

/--
info: ul[item(*)[para[text("one")]]]
ul[item(-)[para[text("two")]]]
ol(4)[item(4.)[para[text("first")]] item(5.)[para[text("second")]]]
dl[desc(:)[text("term")|para[text("description body")]]]
-/
#guard_msgs in
#eval checkParsed "* one\n\n- two\n\n4. first\n5. second\n\n: term\n\n  description body"

/--
info: quote(>)[para[text("quoted text")]]
codeblock(scheme)(flag(+flag, true))[```|"(define x 4)\n"|```]
codeblock([anonymous])()[```|"plain code\n"|```]
directive(note)(named(a:=num(1), parens))[:::|para[text("Inner.")]|:::]
command(cmd)(anon(num(42)))[{|}]
-/
#guard_msgs in
#eval checkParsed
  "> quoted text\n\n```scheme +flag\n(define x 4)\n```\n\n```\nplain code\n```\n\n:::note (a := 1)\nInner.\n:::\n\n{cmd 42}"

/--
info: linkRef("myref":="https://example.com")[[|]:]
footnoteRef("note")[[^|]:|text("the note text")]
-/
#guard_msgs in
#eval checkParsed "[myref]: https://example.com\n\n[^note]: the note text"

/--
info: header(0)[#|text("H")]
metadata(n=1)[%%%|%%%]
-/
#guard_msgs in
#eval checkParsed "# H\n%%%\nauthors := \"me\"\n%%%\n"

section Quotations

open Elab Command

/-- A text element containing `value`. -/
def text (value : String) : CommandElabM (TSyntax ``Parser.inline) := do
  `(Parser.inline| $(← mkVersoTextFromRef value):versoText)

/-- A paragraph whose only content is the text `value`. -/
def para (value : String) : CommandElabM (TSyntax ``Parser.block) := do
  let content : TSyntaxArray ``Parser.inline := #[← text value]
  `(Parser.block| $[$content]*)

/--
info: role(lit)(named(k:=name(v), parens) flag(+on, true) anon(num(3)))[{}[]|code[`|"quoted"|`] text("txt")]
-/
#guard_msgs in
#eval show CommandElabM Unit from do
  let content : TSyntaxArray ``Parser.inline :=
    #[← `(Parser.inline| `$(← mkVersoCodeFromRef "quoted")`), ← text "txt"]
  let stx ← `(Parser.inline| {lit (k := v) +on 3}[$[$content]*])
  IO.println (describeInline stx)

/--
info: emph[_|text("i") linebreak("\n")|_]
bold[*|link[[|text("x")|]|ref("r")[[|]]]|*]
math(display)[$$|`|"m"|`]
image("alt")[![|]|url("u")[(|)]]
footnote("q")[[^|]]
-/
#guard_msgs in
#eval show CommandElabM Unit from do
  let emphasized : TSyntaxArray ``Parser.inline := #[← text "i", ← mkVersoLinebreakFromRef]
  let linked : TSyntaxArray ``Parser.inline := #[← text "x"]
  let bolded : TSyntaxArray ``Parser.inline :=
    #[← `(Parser.inline| [$[$linked]*][$(← mkVersoRefNameFromRef "r")])]
  let inlines : List (TSyntax ``Parser.inline) := [
      ← `(Parser.inline| _$[$emphasized]*_),
      ← `(Parser.inline| *$[$bolded]**),
      ← `(Parser.inline| $$`$(← mkVersoCodeFromRef "m")`),
      ← `(Parser.inline| ![$(← mkVersoImageAltFromRef "alt")]($(← mkVersoLinkUrlFromRef "u"))),
      ← `(Parser.inline| [^$(← mkVersoRefNameFromRef "q")])]
  for i in inlines do
    IO.println (describeInline i)

/--
info: para[text("hi")]
header(2)[###|text("t")]
ul[item(*)[para[text("a")]] item(*)[para[text("b")]]]
ol(3)[item(3.)[para[text("x")]]]
dl[desc(:)[text("t")|para[text("d")]]]
quote(>)[para[text("q")]]
codeblock(lean)(anon(str("arg")))[```|"code\n"|```]
codeblock([anonymous])()[```|"plain"|```]
directive(dir)(flag(-f, false))[:::|para[text("inner")]|:::]
command(go)()[{|}]
linkRef("n":="u")[[|]:]
footnoteRef("n")[[^|]:|text("fn")]
-/
#guard_msgs in
#eval show CommandElabM Unit from do
  let heading : TSyntaxArray ``Parser.inline := #[← text "t"]
  -- A list item's contents swallow a marker that follows them, so sibling items are spliced in.
  let unordered : TSyntaxArray ``Parser.ListItem.item :=
    #[← `(Parser.ListItem.item| * $[$(#[← para "a"])]*),
      ← `(Parser.ListItem.item| * $[$(#[← para "b"])]*)]
  let ordered : TSyntaxArray ``Parser.ListItem.item :=
    #[← `(Parser.ListItem.item| 3. $[$(#[← para "x"])]*)]
  let term : TSyntaxArray ``Parser.inline := #[← text "t"]
  let description : TSyntaxArray ``Parser.block := #[← para "d"]
  let quoted : TSyntaxArray ``Parser.block := #[← para "q"]
  let inner : TSyntaxArray ``Parser.block := #[← para "inner"]
  let note : TSyntaxArray ``Parser.inline := #[← text "fn"]
  let blocks : List (TSyntax ``Parser.block) := [
      ← para "hi",
      ← `(Parser.block| ### $[$heading]*),
      ← `(Parser.Block.ul| $[$unordered:ListItem.item]*),
      ← `(Parser.Block.ol| $[$ordered:ListItem.item]*),
      ← `(Parser.Block.dl| : $[$term]* $[$description:block]*),
      ← `(Parser.block| > $[$quoted]*),
      ← `(Parser.block| ```lean "arg" $(← mkVersoCodeBlockFromRef "code\n"):versoCodeBlock```),
      ← `(Parser.block| ```$(← mkVersoCodeBlockFromRef "plain"):versoCodeBlock```),
      ← `(Parser.block| :::dir -f $[$inner:block]* :::),
      ← `(Parser.block| {go}),
      ← `(Parser.block| [$(← mkVersoRefNameFromRef "n")]: $(← mkVersoLinkRefUrlFromRef "u")),
      ← `(Parser.block| [^$(← mkVersoRefNameFromRef "n")]: $[$note]*)]
  for b in blocks do
    IO.println (describeBlock b)

end Quotations

open Elab Command

/-!
The view of a whole document is the sequence of its blocks, from either producer. Anything that is
not a sequence of blocks is not a document.
-/

def describeDoc (stx : VersoDocument) : String :=
  s!"doc[{" ".intercalate (stx.getVersoBlocks.map (describeBlock ·)).toList}]"

/--
info: doc[header(0)[#|text("Title")] para[text("body") linebreak("\n")]]
doc[para[text("hi")] para[text("there")]]
doc[]
-/
#guard_msgs in
#eval show CommandElabM Unit from do
  let ictx := mkInputContext "# Title\n\nbody\n" "<input>"
  let env ← getEnv
  let s := documentFn.run ictx {env, options := {}} (getTokenTable env) (mkParserState ictx.input)
  IO.println (describeDoc ⟨s.stxStack.back⟩)
  let hi ← para "hi"
  let there ← para "there"
  IO.println (describeDoc (← `(Lean.Doc.Parser.document| $hi $there)))
  IO.println (describeDoc (← `(Lean.Doc.Parser.document| )))
