/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Thrane Christiansen
-/

module

prelude
public import Lean.DocString.Types
public import Lean.Parser.Term.Basic
public import Lean.DocString.Syntax
meta import Lean.DocString.Syntax

set_option linter.missingDocs true

namespace Lean.Doc

open scoped Lean.Doc.Syntax

public section

/-!
This module defines views of the concrete syntax of Verso documents.

The syntax declarations in `Lean.DocString.Syntax` specify the shapes of the trees that the Verso
parser and quotations produce. Views expose one level of this structure at a time as ordinary Lean
datatypes. Each view node records the syntax it represents, the delimiter atoms that tooling such as
semantic highlighting needs, and decoded values for literal content. Using views allows clients to
avoid needing to check for things like optional brackets at all sites.

An `of` function returns `none` when the syntax does not have the specified shape. The parser and
quotations produce only well-formed trees, so a `none` result indicates a bug. Callers report it as
an error at the syntax in question.
-/

/--
A view of the value of an argument to a role, directive, command, or code block.
-/
inductive ArgValView where
  /-- A string literal. `value` is its decoded contents. -/
  | str (lit : StrLit) (value : String)
  /-- An identifier. -/
  | name (x : Ident)
  /-- A numeric literal. `value` is its decoded value. -/
  | num (lit : NumLit) (value : Nat)

/--
A view of `stx`, if it is an argument value.
-/
def ArgValView.of (stx : TSyntax ``Parser.argVal) : Option ArgValView :=
  match stx with
  | `(Parser.ArgVal.ident| $x:ident) => some (.name x)
  | `(Parser.ArgVal.num| $n:num) => some (.num n n.getNat)
  | `(Parser.ArgVal.str| $s:str) => some (.str s s.getString)
  | _ => none

/--
A view of an argument to a role, directive, command, or code block.
-/
inductive ArgView where
  /-- An anonymous positional argument. -/
  | anon (stx : TSyntax ``Parser.arg)
      (val : TSyntax ``Parser.argVal)
  /--
  A named argument. `parens` is the pair of parenthesis atoms when the argument is written in
  parentheses, and `assign` is the `:=` atom.
  -/
  | named (stx : TSyntax ``Parser.arg)
      (parens : Option (Syntax × Syntax)) (name : Ident) (assign : Syntax)
      (val : TSyntax ``Parser.argVal)
  /-- A flag. `sign` is the `+` or `-` atom, and `isOn` indicates which one it is. -/
  | flag (stx : TSyntax ``Parser.arg) (sign : Syntax) (name : Ident)
      (isOn : Bool)

/--
Returns the syntax underlying an argument view.
-/
def ArgView.stx : ArgView → TSyntax ``Parser.arg
  | .anon stx .. | .named stx .. | .flag stx .. => stx

/--
A view of `stx`, if it is an argument.
-/
def ArgView.of (stx : TSyntax ``Parser.arg) : Option ArgView :=
  match stx with
  | `(Parser.Arg.anon| $v:argVal) => some (.anon stx v)
  | `(Parser.Arg.named| (%$po $x:ident :=%$eq $v:argVal )%$pc) =>
    some (.named stx (some (po, pc)) x eq v)
  | `(Parser.Arg.named_no_paren| $x:ident :=%$eq $v:argVal) => some (.named stx none x eq v)
  | `(Parser.Arg.flag_on| +%$tk $x:ident) => some (.flag stx tk x true)
  | `(Parser.Arg.flag_off| -%$tk $x:ident) => some (.flag stx tk x false)
  | _ => none

/--
A view of a link target, which is either a URL or a reference to a URL defined elsewhere.
-/
inductive LinkTargetView where
  /-- A URL written directly, in parentheses. Use `TSyntax.getVersoLinkUrl` to read it. -/
  | url (stx : TSyntax ``Parser.linkTarget) (opener : Syntax)
      (url : VersoLinkUrl) (closer : Syntax)
  /--
  A reference to a URL defined elsewhere, in square brackets. Use `TSyntax.getVersoRefName` to read
  the name.
  -/
  | ref (stx : TSyntax ``Parser.linkTarget) (opener : Syntax)
      (name : VersoRefName) (closer : Syntax)

/--
Builds a delimiter node of kind `kind` that contains `text`, at the position of `tok`.

A delimiter node contains one atom, whose characters are the delimiter that the element denotes. The
`Lean.Doc.Syntax` encoding writes those characters as part of a longer atom, so the node built here
records the delimiter alone and keeps the position of the atom the source wrote.
-/
private def asDelimiter (kind : SyntaxNodeKind) (text : String) (tok : Syntax) : Syntax :=
  let info := tok.getHeadInfo
  .node info kind #[.atom info text]

/--
Builds the backtick delimiter of an inline code element whose content is `value`. A delimiter is
one backtick longer than the longest run of backticks in the content.
-/
private def asCodeDelimiter (value : String) (tok : Syntax) : Syntax :=
  asDelimiter ``Parser.codeDelimiter
    ("".pushn '`' (longestBacktickRun value + 1)) tok

/-- Builds the backtick fence of a code block. -/
private def asFence (tok : Syntax) : Syntax :=
  asDelimiter ``Parser.codeBlockFence "```" tok

/--
Builds a directive's colon delimiter. The `Lean.Doc.Syntax` encoding closes a directive with a
brace, and both delimiters of a directive are the same run of colons.
-/
private def asDirectiveDelimiter (tok : Syntax) : Syntax :=
  asDelimiter ``Parser.directiveDelimiter ":::" tok

/--
Source info for a literal content token that stands in for a string literal written in a quotation.
The token the content came from supplies the positions and the canonicality. In macro-generated
syntax the positions do not point at the content, and code that reparses content relies on that
difference.
-/
private def decodedInfo (tok : Syntax) : SourceInfo :=
  match tok.getHeadInfo, tok.getPos?, tok.getTailPos? with
  | .original leading _ trailing _, some b, some e =>
    .original { leading with startPos := b, stopPos := b } b
      { trailing with startPos := e, stopPos := e } e
  | .synthetic _ _ canonical, some b, some e => .synthetic b e (canonical := canonical)
  | _, _, _ => .none

/--
Builds a string literal whose contents are `value`, positioned at the literal content token `tok` it
was decoded from. Extensions that reparse content take a `StrLit`, so each caller builds one where
it needs one.
-/
def strLitOfContent (value : String) (tok : Syntax) : StrLit :=
  Syntax.mkStrLit value (info := decodedInfo tok)

/--
Creates source info for the content of empty code blocks.

A code block contains a sequence of lines. When that sequence is empty, the code block denotes the
empty string, which sits immediately before the code block's closing fence (here, `tok`).
-/
private def emptyContentInfo (tok : Syntax) : SourceInfo :=
  match tok.getHeadInfo, tok.getPos? with
  | .original leading _ _ _, some b =>
    .original { leading with startPos := b, stopPos := b } b
      { leading with startPos := b, stopPos := b } b
  | .synthetic _ _ canonical, some b => .synthetic b b (canonical := canonical)
  | _, _ => .none

/--
Escapes `value` so that `TSyntax.getVersoText` reads it back unchanged. Only the escape character
itself needs escaping, since decoding drops the backslash from any pair.
-/
private def escapeVersoText (value : String) : String :=
  value.foldl (init := "") fun out c => if c == '\\' then out ++ "\\\\" else out.push c


/--
Builds a text content token for `value`, positioned at `tok`. The token presents content written as
a string literal through the same accessors as content that the parser read from the source.
-/
private def asVersoText (value : String) (tok : Syntax) : VersoText :=
  ⟨Syntax.mkLit versoTextKind (escapeVersoText value) (info := decodedInfo tok)⟩

/--
Builds a verbatim content token for `value`, positioned at `tok`. A document uses the content as
written, so the token records `value` unchanged.
-/
private def asVersoRefName (value : String) (tok : Syntax) : VersoRefName :=
  ⟨Syntax.mkLit versoRefKind value (info := decodedInfo tok)⟩

/-- Builds a link URL token for `value`, positioned at `tok`. -/
private def asVersoLinkUrl (value : String) (tok : Syntax) : VersoLinkUrl :=
  ⟨Syntax.mkLit versoLinkUrlKind (escapeVersoLinkUrl value) (info := decodedInfo tok)⟩

/-- Builds an image alternate text token for `value`, positioned at `tok`. -/
private def asVersoImageAlt (value : String) (tok : Syntax) : VersoImageAlt :=
  ⟨Syntax.mkLit versoImageAltKind (escapeVersoImageAlt value) (info := decodedInfo tok)⟩

/--
Builds a link reference URL token for `value`, positioned at `tok`. Such a URL has no escapes, so
the token records `value` unchanged.
-/
private def asVersoLinkRefUrl (value : String) (tok : Syntax) : VersoLinkRefUrl :=
  ⟨Syntax.mkLit versoLinkRefUrlKind value (info := decodedInfo tok)⟩

/--
Builds an inline code content token for `value`, positioned at `tok`. Decoding strips one space
from each end of content that begins and ends with a space, so the token stores such content with an
extra space at each end.
-/
private def asVersoCode (value : String) (tok : Syntax) : VersoCode :=
  let padded :=
    if versoCodeBoundarySpaces value then " " ++ value ++ " " else value
  ⟨Syntax.mkLit versoCodeKind padded (info := decodedInfo tok)⟩

/--
Builds a code block content token for `value`, positioned at `tok`.
-/
private def asVersoCodeBlock (value : String) (tok : Syntax) : VersoCodeBlock :=
  let line := Syntax.mkLit versoCodeBlockLineKind value (info := decodedInfo tok)
  ⟨Syntax.node (decodedInfo tok) versoCodeBlockKind #[mkNullNode #[line]]⟩

/-- An atom containing `text`, at the position of `tok`. -/
private def asAtom (text : String) (tok : Syntax) : Syntax :=
  .atom tok.getHeadInfo text

/-- A node of kind `kind` whose children are `args`. -/
private def asNode (kind : SyntaxNodeKind) (args : Array Syntax) : Syntax :=
  .node .none kind args

/-!
The functions below rewrite the `Lean.Doc.Syntax` encoding, which quotations produce, into the
encoding that the Verso parser produces. Both encodings describe the same documents. They differ in
which characters the atoms contain, in where the delimiters sit, and in how literal content is
stored.

Syntax that is already in the parser's encoding passes through unchanged, so a caller rewrites a
tree once and then reads only parser syntax.
-/

mutual
  /-- Rewrites an argument value. -/
  partial def argValToParser (stx : Syntax) : Syntax :=
    match stx with
    | `(arg_val|$x:ident) => asNode ``Parser.ArgVal.ident #[x]
    | `(arg_val|$n:num) => asNode ``Parser.ArgVal.num #[n]
    | `(arg_val|$s:str) => asNode ``Parser.ArgVal.str #[s]
    | _ => stx

  /-- Rewrites an argument. -/
  partial def docArgToParser (stx : Syntax) : Syntax :=
    match stx with
    | `(doc_arg|$v:arg_val) => asNode ``Parser.Arg.anon #[argValToParser v]
    | `(doc_arg|(%$po $x:ident :=%$eq $v:arg_val )%$pc) =>
      asNode ``Parser.Arg.named #[po, x, eq, argValToParser v, pc]
    | `(doc_arg|$x:ident :=%$eq $v:arg_val) =>
      asNode ``Parser.Arg.named_no_paren #[x, eq, argValToParser v]
    | `(doc_arg|+%$tk$x:ident) => asNode ``Parser.Arg.flag_on #[tk, x]
    | `(doc_arg|-%$tk$x:ident) => asNode ``Parser.Arg.flag_off #[tk, x]
    | _ => stx

  /-- Rewrites the target of a link or an image. -/
  partial def linkTargetToParser (stx : Syntax) : Syntax :=
    match stx with
    | `(link_target|(%$o $url )%$c) =>
      asNode ``Parser.LinkTarget.url #[o, asVersoLinkUrl url.getString url, c]
    | `(link_target|[%$o $name ]%$c) =>
      asNode ``Parser.LinkTarget.ref #[o, asVersoRefName name.getString name, c]
    | _ => stx

  /-- Rewrites an inline element. -/
  partial def inlineToParser (stx : Syntax) : Syntax :=
    match stx with
    | `(inline|$s:str) => asNode ``Parser.Inline.text #[asVersoText s.getString s]
    | `(inline|_[%$o $inl* ]%$c) =>
      asNode ``Parser.Inline.emph
        #[asDelimiter ``Parser.emphDelimiter "_" o, inlines inl,
          asDelimiter ``Parser.emphDelimiter "_" c]
    | `(inline|*[%$o $inl* ]%$c) =>
      asNode ``Parser.Inline.bold
        #[asDelimiter ``Parser.boldDelimiter "*" o, inlines inl,
          asDelimiter ``Parser.boldDelimiter "*" c]
    | `(inline|code(%$o $s )%$c) => code o s c
    | `(inline|\math%$m code(%$o $s )%$c) =>
      asNode ``Parser.Inline.inline_math
        #[asDelimiter ``Parser.inlineMathMarker "$" m, code o s c]
    | `(inline|\displaymath%$m code(%$o $s )%$c) =>
      asNode ``Parser.Inline.display_math
        #[asDelimiter ``Parser.displayMathMarker "$$" m, code o s c]
    | `(inline|link[%$o $inl* ]%$c $tgt:link_target) =>
      asNode ``Parser.Inline.link
        #[asAtom "[" o, inlines inl, asAtom "]" c, linkTargetToParser tgt]
    | `(inline|image(%$o $alt )%$c $tgt:link_target) =>
      asNode ``Parser.Inline.image
        #[asAtom "![" o, asVersoImageAlt alt.getString alt, asAtom "]" c,
          linkTargetToParser tgt]
    | `(inline|footnote(%$o $name )%$c) =>
      asNode ``Parser.Inline.footnote
        #[asAtom "[^" o, asVersoRefName name.getString name, asAtom "]" c]
    | `(inline|line!$s) =>
      asNode ``Parser.Inline.linebreak #[.atom (decodedInfo s.raw) s.getString]
    | `(inline|role{%$bo $name $args* }%$bc [%$so $inl* ]%$sc) =>
      -- Each bracket sits in a group of its own, which is empty where the source omitted it.
      asNode ``Parser.Inline.role
        #[asAtom "{" bo, name, mkNullNode (args.map (docArgToParser ·)), asAtom "}" bc,
          mkNullNode #[asAtom "[" so], inlines inl, mkNullNode #[asAtom "]" sc]]
    | _ => stx
  where
    inlines (inl : Array Syntax) : Syntax := mkNullNode (inl.map inlineToParser)
    code (o : Syntax) (s : StrLit) (c : Syntax) : Syntax :=
      asNode ``Parser.Inline.code
        #[asCodeDelimiter s.getString o, asVersoCode s.getString s,
          asCodeDelimiter s.getString c]

  /-- Rewrites an item of an ordered or unordered list, giving it the marker `marker`. -/
  partial def listItemToParser (marker : String) (stx : Syntax) : Syntax :=
    match stx with
    | `(list_item|*%$m $bs*) =>
      asNode ``Parser.ListItem.item
        #[asDelimiter ``Parser.listMarker marker m, mkNullNode (bs.map (blockToParser ·))]
    | _ => stx

  /-- Rewrites an item of a description list. -/
  partial def descItemToParser (stx : Syntax) : Syntax :=
    match stx with
    | `(desc_item|:%$marker $term* => $desc*) =>
      asNode ``Parser.DescItem.item
        #[marker, mkNullNode (term.map (inlineToParser ·)),
          mkNullNode (desc.map (blockToParser ·))]
    | _ => stx

  /-- Rewrites a block-level element. -/
  partial def blockToParser (stx : Syntax) : Syntax :=
    match stx with
    | `(block|para[$inls*]) =>
      asNode ``Parser.Block.para #[mkNullNode (inls.map (inlineToParser ·))]
    | `(block| >%$gt $bs*) =>
      asNode ``Parser.Block.blockquote #[gt, blocks bs]
    | `(block|ul{$items*}) =>
      asNode ``Parser.Block.ul #[mkNullNode (items.map (listItemToParser "*" ·))]
    | `(block|ol($n){$items*}) =>
      -- The parser reads an ordered list's first number from the marker of its first item.
      let numbered := items.mapIdx fun i item => listItemToParser s!"{n.getNat + i}." item
      asNode ``Parser.Block.ol #[mkNullNode numbered]
    | `(block|dl{$items*}) =>
      asNode ``Parser.Block.dl #[mkNullNode (items.map (descItemToParser ·))]
    | `(block| ```%$o | $s ```%$c) =>
      asNode ``Parser.Block.codeblock
        #[asFence o, mkNullNode #[], asVersoCodeBlock s.getString s, asFence c]
    | `(block| ```%$o $name $args* | $s ```%$c) =>
      asNode ``Parser.Block.codeblock
        #[asFence o, mkNullNode #[name, mkNullNode (args.map (docArgToParser ·))],
          asVersoCodeBlock s.getString s, asFence c]
    | `(block| :::%$o $name $args* {$bs*}%$c) =>
      asNode ``Parser.Block.directive
        #[asDirectiveDelimiter o, name, mkNullNode (args.map (docArgToParser ·)), blocks bs,
          asDirectiveDelimiter c]
    | `(block|command{%$bo $name $args* }%$bc) =>
      asNode ``Parser.Block.command
        #[asAtom "{" bo, name, mkNullNode (args.map (docArgToParser ·)), asAtom "}" bc]
    | `(block|header(%$tok $n ){$inls*}) =>
      asNode ``Parser.Block.header
        #[asDelimiter ``Parser.headerMarker ("".pushn '#' (n.getNat + 1)) tok,
          mkNullNode (inls.map (inlineToParser ·))]
    | `(block|[%$o $name ]:%$closer $url) =>
      asNode ``Parser.Block.link_ref
        #[o, asVersoRefName name.getString name, closer, asVersoLinkRefUrl url.getString url]
    | `(block|[^%$o $name ]:%$closer $inls*) =>
      asNode ``Parser.Block.footnote_ref
        #[o, asVersoRefName name.getString name, closer,
          mkNullNode (inls.map (inlineToParser ·))]
    -- Both encodings store the metadata in one `structInstFields` node, which wraps the fields and
    -- the separators between them.
    | `(block|%%%%$o $contents* %%%%$c) =>
      asNode ``Parser.Block.metadata_block
        #[o, asNode ``Lean.Parser.Term.structInstFields #[mkNullNode contents], c]
    | _ => stx
  where
    blocks (bs : Array Syntax) : Syntax := mkNullNode (bs.map blockToParser)
end

/-!
Document syntax in the `Lean.Doc.Syntax` encoding converts to the encoding that the Verso parser
produces, so that code that reads documents names only the parser's kinds.
-/

instance : Coe (TSyntax `arg_val) (TSyntax ``Parser.argVal) where
  coe s := ⟨argValToParser s.raw⟩

instance : Coe (TSyntax `doc_arg) (TSyntax ``Parser.arg) where
  coe s := ⟨docArgToParser s.raw⟩

instance : Coe (TSyntax `link_target) (TSyntax ``Parser.linkTarget) where
  coe s := ⟨linkTargetToParser s.raw⟩

instance : Coe (TSyntax `inline) (TSyntax ``Parser.inline) where
  coe s := ⟨inlineToParser s.raw⟩

instance : Coe (TSyntax `list_item) (TSyntax ``Parser.ListItem.item) where
  coe s := ⟨listItemToParser "*" s.raw⟩

instance : Coe (TSyntax `desc_item) (TSyntax ``Parser.DescItem.item) where
  coe s := ⟨descItemToParser s.raw⟩

instance : Coe (TSyntax `block) (TSyntax ``Parser.block) where
  coe s := ⟨blockToParser s.raw⟩

instance : Coe (TSyntaxArray `doc_arg) (TSyntaxArray ``Parser.arg) where
  coe xs := xs.map (↑·)

instance : Coe (TSyntaxArray `inline) (TSyntaxArray ``Parser.inline) where
  coe xs := xs.map (↑·)

instance : Coe (TSyntaxArray `block) (TSyntaxArray ``Parser.block) where
  coe xs := xs.map (↑·)

section Migration
/-
The definitions in this section are temporary bootstrapping adaptation functions. After a stage0
update, a wrapper can receive the parser's kinds and the content tokens directly, and these can be
deleted: the first pair along with the contents of Lean.Doc.Syntax, the second pair once no wrapper
receives literal content as a string literal.
-/

/-- Migrates inline elements to the encoding that the Verso parser produces. -/
def migrateInlines (xs : TSyntaxArray `inline) : TSyntaxArray ``Parser.inline := ↑xs

/-- Migrates block-level elements to the encoding that the Verso parser produces. -/
def migrateBlocks (xs : TSyntaxArray `block) : TSyntaxArray ``Parser.block := ↑xs

/-- Presents a string literal's contents as an inline code content token. -/
def versoCodeOfStrLit (s : StrLit) : VersoCode := asVersoCode s.getString s

/-- Presents a string literal's contents as a code block content token. -/
def versoCodeBlockOfStrLit (s : StrLit) : VersoCodeBlock := asVersoCodeBlock s.getString s

end Migration
/--
A view of `stx`, if it is a link target.
-/
def LinkTargetView.of (stx : TSyntax ``Parser.linkTarget) : Option LinkTargetView :=
  match stx with
  | `(Parser.LinkTarget.url| (%$o $url:versoLinkUrl )%$c) => some (.url stx o url c)
  | `(Parser.LinkTarget.ref| [%$o $name:versoRef ]%$c) => some (.ref stx o name c)
  | _ => none

/--
Narrows the recorded range of an inline code element's content token to the value it denotes. Where
decoding strips boundary spaces, the range shrinks by one character on each side, so that it still
delimits the region the value comes from.
-/
private def narrowToValue (content : VersoCode) : VersoCode :=
  let raw := (Syntax.isLit? versoCodeKind content.raw).getD ""
  if raw.length == content.getVersoCode.length then content
  else
    match content.raw with
    | .node info k #[.atom atomInfo val] =>
      ⟨.node (shrink info) k #[.atom (shrink atomInfo) val]⟩
    | _ => content
where
  shrink : SourceInfo → SourceInfo
    | .original leading start trailing stop =>
      .original
        { leading with stopPos := leading.stopPos.offsetBy ⟨1⟩ } (start.offsetBy ⟨1⟩)
        { trailing with startPos := trailing.startPos.unoffsetBy ⟨1⟩ } (stop.unoffsetBy ⟨1⟩)
    | .synthetic start stop canonical =>
      .synthetic (start.offsetBy ⟨1⟩) (stop.unoffsetBy ⟨1⟩) canonical
    | .none => .none

/--
A view of ordinary text.
-/
structure TextView where
  /-- The original syntax. -/
  stx : TSyntax ``Parser.inline
  /-- The text. -/
  content : VersoText

/-- Decodes the Verso text contained in the view, interpreting escape sequences. -/
def TextView.getVersoText (v : TextView) : String := v.content.getVersoText

/--
Returns the literal representation of the text in the view, without interpreting escape sequences.
-/
def TextView.getVersoTextSource (v : TextView) : String := v.content.getVersoTextSource

/-- A view of `stx`, if it is ordinary text. -/
def TextView.of (stx : TSyntax ``Parser.inline) : Option TextView :=
  match stx with
  | `(Parser.Inline.text| $s:versoText) => some { stx, content := s }
  | _ => none

/--
A view of emphasized content.
-/
structure EmphView where
  /-- The original syntax. -/
  stx : TSyntax ``Parser.inline
  /-- The opening run of `_`. -/
  opener : TSyntax ``Parser.emphDelimiter
  /-- The emphasized content. -/
  content : TSyntaxArray ``Parser.inline
  /-- The closing run of `_`. -/
  closer : TSyntax ``Parser.emphDelimiter

/-- A view of `stx`, if it is emphasized content. -/
def EmphView.of (stx : TSyntax ``Parser.inline) : Option EmphView :=
  match stx with
  | `(Parser.Inline.emph| $o:emphDelimiter $inl* $c:emphDelimiter) =>
    some { stx, opener := o, content := inl, closer := c }
  | _ => none

/--
A view of bold content.
-/
structure BoldView where
  /-- The original syntax. -/
  stx : TSyntax ``Parser.inline
  /-- The opening run of `*`. -/
  opener : TSyntax ``Parser.boldDelimiter
  /-- The bold content. -/
  content : TSyntaxArray ``Parser.inline
  /-- The closing run of `*`. -/
  closer : TSyntax ``Parser.boldDelimiter

/-- A view of `stx`, if it is bold content. -/
def BoldView.of (stx : TSyntax ``Parser.inline) : Option BoldView :=
  match stx with
  | `(Parser.Inline.bold| $o:boldDelimiter $inl* $c:boldDelimiter) =>
    some { stx, opener := o, content := inl, closer := c }
  | _ => none

/--
A view of literal code.

This view is used both for inline code elements and the body of math notation.
-/
structure CodeView where
  /-- The original syntax. -/
  stx : TSyntax ``Parser.inline
  /-- The opening run of backticks. -/
  opener : TSyntax ``Parser.codeDelimiter
  /-- The code. -/
  content : VersoCode
  /-- The closing run of backticks. -/
  closer : TSyntax ``Parser.codeDelimiter

/-- The decoded code contents -/
def CodeView.getVersoCode (v : CodeView) : String := v.content.getVersoCode

/-- A view of `stx`, if it is inline code. -/
def CodeView.of (stx : TSyntax ``Parser.inline) : Option CodeView :=
  match stx with
  | `(Parser.Inline.code| $o:codeDelimiter $s:versoCode $c:codeDelimiter) =>
    some { stx, opener := o, content := narrowToValue s, closer := c }
  | _ => none

/--
A view of math content.
-/
structure MathView where
  /-- The original syntax. -/
  stx : TSyntax ``Parser.inline
  /-- Whether the mathematics should be typeset in inline or display mode. -/
  mode : MathMode
  /-- The `$` or `$$` marker. -/
  marker : TSyntax [``Parser.inlineMathMarker, ``Parser.displayMathMarker]
  /-- The LaTeX-style math code. -/
  code : CodeView

/-- The decoded code contents. -/
def MathView.getVersoCode (v : MathView) : String := v.code.getVersoCode

/--
A view of `stx`, if it is math content.

Math nests a code element, so the view contains the view of that element.
-/
def MathView.of (stx : TSyntax ``Parser.inline) : Option MathView := do
  match stx with
  | `(Parser.Inline.inline_math| $m:inlineMathMarker $c:code) =>
    return { stx, mode := .inline, marker := m, code := ← CodeView.of ⟨c.raw⟩ }
  | `(Parser.Inline.display_math| $m:displayMathMarker $c:code) =>
    return { stx, mode := .display, marker := m, code := ← CodeView.of ⟨c.raw⟩ }
  | _ => none

/--
A view of a link.
-/
structure LinkView where
  /-- The original syntax. -/
  stx : TSyntax ``Parser.inline
  /-- The `[` that opens the link text. -/
  opener : Syntax
  /-- The link text. -/
  content : TSyntaxArray ``Parser.inline
  /-- The `]` that closes the link text. -/
  closer : Syntax
  /-- Where the link leads. -/
  target : LinkTargetView

/-- A view of `stx`, if it is a link. -/
def LinkView.of (stx : TSyntax ``Parser.inline) : Option LinkView := do
  match stx with
  | `(Parser.Inline.link| [%$o $inl* ]%$c $tgt:linkTarget) =>
    return { stx, opener := o, content := inl, closer := c, target := ← LinkTargetView.of tgt }
  | _ => none

/--
A view of an image.
-/
structure ImageView where
  /-- The original syntax. -/
  stx : TSyntax ``Parser.inline
  /-- The `![` that opens the alternate text. -/
  opener : Syntax
  /-- The alternate text. -/
  alt : VersoImageAlt
  /-- The `]` that closes the alternate text. -/
  closer : Syntax
  /-- Where the image is found. -/
  target : LinkTargetView

/-- The alternate text, with each escape replaced by the character it denotes. -/
def ImageView.getAlt (v : ImageView) : String := v.alt.getVersoImageAlt

/-- A view of `stx`, if it is an image. -/
def ImageView.of (stx : TSyntax ``Parser.inline) : Option ImageView := do
  match stx with
  | `(Parser.Inline.image| ![%$o $alt:versoImageAlt ]%$c $tgt:linkTarget) =>
    return { stx, opener := o, alt, closer := c, target := ← LinkTargetView.of tgt }
  | _ => none

/--
A view of a footnote use site.
-/
structure FootnoteView where
  /-- The original syntax. -/
  stx : TSyntax ``Parser.inline
  /-- The `[^` that opens the name. -/
  opener : Syntax
  /-- The name that refers to the footnote's definition. -/
  name : VersoRefName
  /-- The `]` that closes the name. -/
  closer : Syntax

/-- The name that refers to the footnote's definition. -/
def FootnoteView.getName (v : FootnoteView) : String := v.name.getVersoRefName

/-- A view of `stx`, if it is a footnote use site. -/
def FootnoteView.of (stx : TSyntax ``Parser.inline) : Option FootnoteView :=
  match stx with
  | `(Parser.Inline.footnote| [^%$o $name:versoRef ]%$c) =>
    some { stx, opener := o, name, closer := c }
  | _ => none

/--
A view of a line break.
-/
structure LinebreakView where
  /-- The original syntax. -/
  stx : TSyntax ``Parser.inline
  /-- The newline atom. -/
  newline : Syntax

/-- A view of `stx`, if it is a line break. -/
def LinebreakView.of (stx : TSyntax ``Parser.inline) : Option LinebreakView :=
  match stx with
  | `(Parser.Inline.linebreak| $nl:linebreak) => some { stx, newline := nl.raw[0] }
  | _ => none

/--
A view of content with a role.
-/
structure RoleView where
  /-- The original syntax. -/
  stx : TSyntax ``Parser.inline
  /-- The `{` that opens the name and arguments. -/
  braceOpen : Syntax
  /-- The name that selects the role's expander. -/
  name : Ident
  /-- The arguments to the role. -/
  args : TSyntaxArray ``Parser.arg
  /-- The `}` that closes the name and arguments. -/
  braceClose : Syntax
  /--
  The brackets around the content, if they are present.
  -/
  brackets : Option (Syntax × Syntax)
  /-- The content that the role applies to. -/
  content : TSyntaxArray ``Parser.inline

/--
A view of `stx`, if it is content with a role.

An author may write content that has delimiters of its own without brackets, so the brackets are
matched separately from the name and arguments.
-/
def RoleView.of (stx : TSyntax ``Parser.inline) : Option RoleView :=
  match stx with
  | `(Parser.Inline.role| {%$bo $name:ident $args* }%$bc [%$so $inl* ]%$sc) =>
    some {
      stx, braceOpen := bo, name, args, braceClose := bc,
      brackets := some (so, sc), content := inl
    }
  | `(Parser.Inline.role| {%$bo $name:ident $args* }%$bc $inl:inline*) =>
    some {
      stx, braceOpen := bo, name, args, braceClose := bc,
      brackets := none, content := inl
    }
  | _ => none

/--
A view of an inline document element.
-/
inductive InlineView where
  /-- Ordinary text. -/
  | text (view : TextView)
  /-- Emphasized content. -/
  | emph (view : EmphView)
  /-- Bold content. -/
  | bold (view : BoldView)
  /-- Literal code. -/
  | code (view : CodeView)
  /-- Mathematical notation. -/
  | math (view : MathView)
  /-- A link. -/
  | link (view : LinkView)
  /-- An image. -/
  | image (view : ImageView)
  /-- A footnote use site. -/
  | footnote (view : FootnoteView)
  /-- A soft line break. -/
  | linebreak (view : LinebreakView)
  /-- A role applied to some content. -/
  | role (view : RoleView)

instance : Coe TextView InlineView := ⟨.text⟩
instance : Coe EmphView InlineView := ⟨.emph⟩
instance : Coe BoldView InlineView := ⟨.bold⟩
instance : Coe CodeView InlineView := ⟨.code⟩
instance : Coe MathView InlineView := ⟨.math⟩
instance : Coe LinkView InlineView := ⟨.link⟩
instance : Coe ImageView InlineView := ⟨.image⟩
instance : Coe FootnoteView InlineView := ⟨.footnote⟩
instance : Coe LinebreakView InlineView := ⟨.linebreak⟩
instance : Coe RoleView InlineView := ⟨.role⟩

/--
Returns the original syntax that an inline view was constructed from.
-/
def InlineView.stx : InlineView → TSyntax ``Parser.inline
  | .text v => v.stx
  | .emph v => v.stx
  | .bold v => v.stx
  | .code v => v.stx
  | .math v => v.stx
  | .link v => v.stx
  | .image v => v.stx
  | .footnote v => v.stx
  | .linebreak v => v.stx
  | .role v => v.stx

/--
A view of `stx`, if it is an inline document element.

Each production has a view of its own, and this tries them in turn. The productions have distinct
syntax kinds, so at most one applies and the order does not matter.
-/
def InlineView.of (stx : TSyntax ``Parser.inline) : Option InlineView :=
  .text <$> TextView.of stx <|>
  .emph <$> EmphView.of stx <|>
  .bold <$> BoldView.of stx <|>
  .code <$> CodeView.of stx <|>
  .math <$> MathView.of stx <|>
  .link <$> LinkView.of stx <|>
  .image <$> ImageView.of stx <|>
  .footnote <$> FootnoteView.of stx <|>
  .linebreak <$> LinebreakView.of stx <|>
  .role <$> RoleView.of stx

/--
A view of an item of an unordered list.
-/
structure UnorderedListItemView where
  /-- The original syntax. -/
  stx : TSyntax ``Parser.ListItem.item
  /-- The marker, which is `*`, `-`, or `+`. -/
  marker : TSyntax ``Parser.listMarker
  /-- The item's contents. -/
  contents : TSyntaxArray ``Parser.block

/--
A view of `stx`, if it is an unordered list's item. Its marker must be a bullet.
-/
def UnorderedListItemView.of (stx : TSyntax ``Parser.ListItem.item) :
    Option UnorderedListItemView :=
  match stx with
  | `(Parser.ListItem.item| $m:listMarker $bs*) =>
    if m.getVersoDelimiter.front? |>.any (· ∈ ['*', '-', '+']) then some ⟨stx, m, bs⟩ else none
  | _ => none

/--
A view of an item of an ordered list.
-/
structure OrderedListItemView where
  /-- The original syntax. -/
  stx : TSyntax ``Parser.ListItem.item
  /-- The marker, which is a number followed by `.` or `)`. -/
  marker : TSyntax ``Parser.listMarker
  /-- The item's contents. -/
  contents : TSyntaxArray ``Parser.block

/-- The number that the item's marker gives it. -/
def OrderedListItemView.number (v : OrderedListItemView) : Option Nat :=
  v.marker.getVersoDelimiter.takeWhile (·.isDigit) |>.copy.toNat?

/--
A view of `stx`, if it is an ordered list's item. Its marker must be a number.
-/
def OrderedListItemView.of (stx : TSyntax ``Parser.ListItem.item) : Option OrderedListItemView :=
  match stx with
  | `(Parser.ListItem.item| $m:listMarker $bs*) =>
    if m.getVersoDelimiter.front? |>.any (·.isDigit) then some ⟨stx, m, bs⟩ else none
  | _ => none

/--
A view of an item description from a description list.
-/
structure DescItemView where
  /-- The original syntax. -/
  stx : TSyntax ``Parser.DescItem.item
  /-- The `:` that introduces the item. -/
  marker : Syntax
  /-- The term that the item describes. -/
  term : TSyntaxArray ``Parser.inline
  /-- The description. -/
  desc : TSyntaxArray ``Parser.block

/--
A view of `stx`, if it is a description list item.
-/
def DescItemView.of (stx : TSyntax ``Parser.DescItem.item) : Option DescItemView :=
  match stx with
  | `(Parser.DescItem.item| :%$marker $term:inline* $desc:block*) =>
    some ⟨stx, marker, term, desc⟩
  | _ => none

/--
A view of a paragraph.
-/
structure ParaView where
  /-- The original syntax. -/
  stx : TSyntax ``Parser.block
  /-- The paragraph's contents. -/
  content : TSyntaxArray ``Parser.inline

/-- A view of `stx`, if it is a paragraph. -/
def ParaView.of (stx : TSyntax ``Parser.block) : Option ParaView :=
  match stx with
  | `(Parser.Block.para| $inl*) => some { stx, content := inl }
  | _ => none

/--
A view of an unordered list.
-/
structure UnorderedListView where
  /-- The original syntax. -/
  stx : TSyntax ``Parser.block
  /-- The list's items. -/
  items : Array UnorderedListItemView

/-- A view of `stx`, if it is an unordered list. -/
def UnorderedListView.of (stx : TSyntax ``Parser.block) : Option UnorderedListView := do
  match stx with
  | `(Parser.Block.ul| $items:ListItem.item*) =>
    return { stx, items := ← items.mapM UnorderedListItemView.of }
  | _ => none

/--
A view of an ordered list.
-/
structure OrderedListView where
  /-- The original syntax. -/
  stx : TSyntax ``Parser.block
  /-- The number of the first item, which the first item's marker gives it. -/
  start : Nat
  /-- The list's items. -/
  items : Array OrderedListItemView

/-- A view of `stx`, if it is an ordered list. -/
def OrderedListView.of (stx : TSyntax ``Parser.block) : Option OrderedListView := do
  match stx with
  | `(Parser.Block.ol| $items:ListItem.item*) =>
    let items ← items.mapM OrderedListItemView.of
    return { stx, start := items[0]?.bind (·.number) |>.getD 1, items }
  | _ => none

/--
A view of a description list.
-/
structure DescListView where
  /-- The original syntax. -/
  stx : TSyntax ``Parser.block
  /-- The list's items. -/
  items : Array DescItemView

/-- A view of `stx`, if it is a description list. -/
def DescListView.of (stx : TSyntax ``Parser.block) : Option DescListView := do
  match stx with
  | `(Parser.Block.dl| $items:DescItem.item*) =>
    return { stx, items := ← items.mapM DescItemView.of }
  | _ => none

/--
A view of a block quotation.
-/
structure BlockquoteView where
  /-- The original syntax. -/
  stx : TSyntax ``Parser.block
  /-- The `>` that introduces the quotation. -/
  marker : Syntax
  /-- The quoted blocks. -/
  content : TSyntaxArray ``Parser.block

/-- A view of `stx`, if it is a block quotation. -/
def BlockquoteView.of (stx : TSyntax ``Parser.block) : Option BlockquoteView :=
  match stx with
  | `(Parser.Block.blockquote| >%$gt $bs*) => some { stx, marker := gt, content := bs }
  | _ => none

/--
A view of a code block.
-/
structure CodeBlockView where
  /-- The original syntax. -/
  stx : TSyntax ``Parser.block
  /-- The opening run of backticks. -/
  openFence : TSyntax ``Parser.codeBlockFence
  /-- The name that selects the code block's expander, where the code block invokes one. -/
  name? : Option Ident
  /-- The arguments to the expander. -/
  args : TSyntaxArray ``Parser.arg
  /-- The code. -/
  content : VersoCodeBlock
  /-- The closing run of backticks. -/
  closeFence : TSyntax ``Parser.codeBlockFence

/-- The code, which is the texts of its lines in order. -/
def CodeBlockView.getVersoCodeBlock (v : CodeBlockView) : String := v.content.getVersoCodeBlock

/-- A view of `stx`, if it is a code block. -/
def CodeBlockView.of (stx : TSyntax ``Parser.block) : Option CodeBlockView :=
  match stx with
  | `(Parser.Block.codeblock| $openFence:codeBlockFence $[$name:ident $args*]? $s:versoCodeBlock
        $closeFence:codeBlockFence) =>
    -- Empty content parses with no tokens of its own, so its location is the closing fence.
    let content : VersoCodeBlock :=
      if s.raw.getPos?.isSome then s else ⟨s.raw.setInfo (emptyContentInfo closeFence)⟩
    some {
      stx, openFence, name? := name, args := args.getD #[], content, closeFence
    }
  | _ => none

/--
A view of a directive.
-/
structure DirectiveView where
  /-- The original syntax. -/
  stx : TSyntax ``Parser.block
  /-- The opening run of colons. -/
  opener : TSyntax ``Parser.directiveDelimiter
  /-- The name that selects the directive's expander. -/
  name : Ident
  /-- The arguments to the directive. -/
  args : TSyntaxArray ``Parser.arg
  /-- The blocks that the directive contains. -/
  content : TSyntaxArray ``Parser.block
  /-- The closing run of colons. -/
  closer : TSyntax ``Parser.directiveDelimiter

/-- A view of `stx`, if it is a directive. -/
def DirectiveView.of (stx : TSyntax ``Parser.block) : Option DirectiveView :=
  match stx with
  | `(Parser.Block.directive| $opener:directiveDelimiter $name:ident $args:arg* $bs:block*
        $closer:directiveDelimiter) =>
    some { stx, opener, name, args, content := bs, closer }
  | _ => none

/--
A view of a block-level command.
-/
structure CommandView where
  /-- The original syntax. -/
  stx : TSyntax ``Parser.block
  /-- The `{` that opens the name and arguments. -/
  braceOpen : Syntax
  /-- The name that selects the command's expander. -/
  name : Ident
  /-- The arguments to the command. -/
  args : TSyntaxArray ``Parser.arg
  /-- The `}` that closes the name and arguments. -/
  braceClose : Syntax

/-- A view of `stx`, if it is a block-level command. -/
def CommandView.of (stx : TSyntax ``Parser.block) : Option CommandView :=
  match stx with
  | `(Parser.Block.command| {%$braceOpen $name:ident $args* }%$braceClose) =>
    some { stx, braceOpen, name, args, braceClose }
  | _ => none

/--
A view of a section header.
-/
structure HeaderView where
  /-- The original syntax. -/
  stx : TSyntax ``Parser.block
  /-- The run of `#` characters. -/
  marker : TSyntax ``Parser.headerMarker
  /-- The header's nesting depth, with `0` denoting a top-level header. -/
  level : Nat
  /-- The header's text. -/
  content : TSyntaxArray ``Parser.inline

/-- A view of `stx`, if it is a section header. -/
def HeaderView.of (stx : TSyntax ``Parser.block) : Option HeaderView :=
  match stx with
  | `(Parser.Block.header| $marker:headerMarker $content*) =>
    -- The header's level is the length of the `#` run that the marker contains.
    some { stx, marker, level := marker.getVersoDelimiter.length - 1, content }
  | _ => none

/--
A view of a named URL that links and images can use.
-/
structure LinkRefView where
  /-- The original syntax. -/
  stx : TSyntax ``Parser.block
  /-- The `[` that opens the name. -/
  opener : Syntax
  /-- The name that a link or image uses to reach the URL. -/
  name : VersoRefName
  /-- The `]:` that closes the name. -/
  closer : Syntax
  /-- The URL. -/
  url : VersoLinkRefUrl

/-- The name that a link or image repeats to reach this URL. -/
def LinkRefView.getName (v : LinkRefView) : String := v.name.getVersoRefName

/-- The URL that the reference provides. -/
def LinkRefView.getUrl (v : LinkRefView) : String := v.url.getVersoLinkRefUrl

/-- A view of `stx`, if it is a named URL. -/
def LinkRefView.of (stx : TSyntax ``Parser.block) : Option LinkRefView :=
  match stx with
  | `(Parser.Block.link_ref| [%$opener $name:versoRef ]:%$closer $url:versoLinkRefUrl) =>
    some { stx, opener, name, closer, url }
  | _ => none

/--
A view of a footnote definition.
-/
structure FootnoteRefView where
  /-- The original syntax. -/
  stx : TSyntax ``Parser.block
  /-- The `[^` that opens the name. -/
  opener : Syntax
  /-- The name of the footnote. -/
  name : VersoRefName
  /-- The `]:` that closes the name. -/
  closer : Syntax
  /-- The footnote's text. -/
  content : TSyntaxArray ``Parser.inline

/-- The name of the footnote. -/
def FootnoteRefView.getName (v : FootnoteRefView) : String := v.name.getVersoRefName

/-- A view of `stx`, if it is a footnote definition. -/
def FootnoteRefView.of (stx : TSyntax ``Parser.block) : Option FootnoteRefView :=
  match stx with
  | `(Parser.Block.footnote_ref| [^%$opener $name:versoRef ]:%$closer $content*) =>
    some { stx, opener, name, closer, content }
  | _ => none

/--
A view of a metadata block for the preceding header.
-/
structure MetadataView where
  /-- The original syntax. -/
  stx : TSyntax ``Parser.block
  /-- The opening `%%%`. -/
  opener : Syntax
  /-- The metadata, written as the fields of a Lean structure instance. -/
  contents : TSyntax ``Lean.Parser.Term.structInstFields
  /-- The closing `%%%`. -/
  closer : Syntax

/-- The individual metadata fields, without their separators. -/
def MetadataView.fields (v : MetadataView) :
    TSyntaxArray ``Lean.Parser.Term.structInstField :=
  v.contents.raw[0].getSepArgs.map (⟨·⟩)

/-- A view of `stx`, if it is a metadata block. -/
def MetadataView.of (stx : TSyntax ``Parser.block) : Option MetadataView :=
  match stx with
  | `(Parser.Block.metadata_block| %%%%$opener $contents:metadataContents %%%%$closer) =>
    some { stx, opener, contents, closer }
  | _ => none

/--
A view of a block-level document element.

Each view records the syntax it is a view of, the delimiter atoms, and decoded values for literal
content. Nested content stays as concrete syntax, for the consumer to view in turn.
-/
inductive BlockView where
  /-- A paragraph. -/
  | para (view : ParaView)
  /-- An unordered list. -/
  | ul (view : UnorderedListView)
  /-- An ordered list. -/
  | ol (view : OrderedListView)
  /-- A description list. -/
  | dl (view : DescListView)
  /-- A block quotation. -/
  | blockquote (view : BlockquoteView)
  /-- A code block. -/
  | codeblock (view : CodeBlockView)
  /-- A directive. -/
  | directive (view : DirectiveView)
  /-- A block-level command. -/
  | command (view : CommandView)
  /-- A section header. -/
  | header (view : HeaderView)
  /-- A named URL that links and images can use. -/
  | linkRef (view : LinkRefView)
  /-- A footnote definition. -/
  | footnoteRef (view : FootnoteRefView)
  /-- A metadata block for the preceding header. -/
  | metadata (view : MetadataView)

instance : Coe ParaView BlockView := ⟨.para⟩
instance : Coe UnorderedListView BlockView := ⟨.ul⟩
instance : Coe OrderedListView BlockView := ⟨.ol⟩
instance : Coe DescListView BlockView := ⟨.dl⟩
instance : Coe BlockquoteView BlockView := ⟨.blockquote⟩
instance : Coe CodeBlockView BlockView := ⟨.codeblock⟩
instance : Coe DirectiveView BlockView := ⟨.directive⟩
instance : Coe CommandView BlockView := ⟨.command⟩
instance : Coe HeaderView BlockView := ⟨.header⟩
instance : Coe LinkRefView BlockView := ⟨.linkRef⟩
instance : Coe FootnoteRefView BlockView := ⟨.footnoteRef⟩
instance : Coe MetadataView BlockView := ⟨.metadata⟩

/--
Returns the syntax underlying a block view.
-/
def BlockView.stx : BlockView → TSyntax ``Parser.block
  | .para v => v.stx
  | .ul v => v.stx
  | .ol v => v.stx
  | .dl v => v.stx
  | .blockquote v => v.stx
  | .codeblock v => v.stx
  | .directive v => v.stx
  | .command v => v.stx
  | .header v => v.stx
  | .linkRef v => v.stx
  | .footnoteRef v => v.stx
  | .metadata v => v.stx

/--
A view of `stx`, if it is a block-level document element.

Each production has a view of its own, and this tries them in turn. The productions have distinct
syntax kinds, so at most one applies and the order does not matter.
-/
def BlockView.of (stx : TSyntax ``Parser.block) : Option BlockView :=
  .para <$> ParaView.of stx <|>
  .ul <$> UnorderedListView.of stx <|>
  .ol <$> OrderedListView.of stx <|>
  .dl <$> DescListView.of stx <|>
  .blockquote <$> BlockquoteView.of stx <|>
  .codeblock <$> CodeBlockView.of stx <|>
  .directive <$> DirectiveView.of stx <|>
  .command <$> CommandView.of stx <|>
  .header <$> HeaderView.of stx <|>
  .linkRef <$> LinkRefView.of stx <|>
  .footnoteRef <$> FootnoteRefView.of stx <|>
  .metadata <$> MetadataView.of stx

end
