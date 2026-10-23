/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich, Marc Huisinga
-/
module

prelude
public import Lean.Server.Requests
public import Lean.Data.Markdown
import Lean.DocString.View
import Lean.DocString.Parser

public section

namespace Lean.Server.FileWorker
open Lsp
open RequestM

/--
`SyntaxNodeKind`s for which the syntax node and its children receive no semantic highlighting.
-/
def noHighlightKinds : Array SyntaxNodeKind := #[
  -- usually have special highlighting by the client
  ``Lean.Parser.Term.sorry,
  ``Lean.Parser.Term.type,
  ``Lean.Parser.Term.prop,
  -- not really keywords
  `antiquotName]

def docKinds : Array SyntaxNodeKind := #[
  ``Lean.Parser.Command.plainDocComment,
  ``Lean.Parser.Command.docComment,
  ``Lean.Parser.Command.moduleDoc
]

-- TODO: make extensible, or don't
/-- Keywords for which a specific semantic token is provided. -/
def keywordSemanticTokenMap : Std.TreeMap String SemanticTokenType :=
  Std.TreeMap.empty
    |>.insert "sorry" .leanSorryLike
    |>.insert "admit" .leanSorryLike
    |>.insert "stop" .leanSorryLike
    |>.insert "#exit" .leanSorryLike

/-- Semantic token information for a source range. -/
structure LeanSemanticToken where
  /-- Source range of the semantic token. -/
  range : Syntax.Range
  /-- Type of the semantic token. -/
  type : SemanticTokenType
  /-- In case of overlap, higher-priority tokens will take precedence -/
  priority : Nat := 5
  /-- Modifiers of the semantic token. -/
  modifiers : List SemanticTokenModifier := []

/-- The semantic token for the source range of `stx`, if it has one. -/
def LeanSemanticToken.ofSyntax? (stx : Syntax) (tokenType : SemanticTokenType) (priority : Nat := 5)
    (modifiers : List SemanticTokenModifier := []) : Option LeanSemanticToken :=
  stx.getRange?.map fun range => { range, type := tokenType, priority, modifiers }

/-- Appends the semantic token for the source range of `stx`, if it has one. -/
def pushSyntaxToken (toks : Array LeanSemanticToken) (stx : Syntax) (tokenType : SemanticTokenType)
    (priority : Nat := 5) (modifiers : List SemanticTokenModifier := []) :
    Array LeanSemanticToken :=
  match LeanSemanticToken.ofSyntax? stx tokenType priority modifiers with
  | some tok => toks.push tok
  | none => toks

/-- Semantic token information with absolute LSP positions. -/
structure AbsoluteLspSemanticToken where
  /-- Start position of the semantic token. -/
  pos     : Lsp.Position
  /-- End position of the semantic token. -/
  tailPos : Lsp.Position
  /-- Type of the semantic token. -/
  type    : SemanticTokenType
  /-- In case of overlap, higher-priority tokens will take precedence -/
  priority : Nat := 5
  /-- The token's modifiers, as the bit set that LSP expects: bit `m.toNat` is set for each modifier `m`. -/
  modifiers : Nat := 0
  deriving BEq, Hashable, FromJson, ToJson

/-- Encodes modifiers as the bit set that LSP expects. -/
private def encodeModifiers (modifiers : List SemanticTokenModifier) : Nat :=
  modifiers.foldl (fun acc m => acc ||| (1 <<< m.toNat)) 0

/--
Given a set of `LeanSemanticToken`, computes the `AbsoluteLspSemanticToken` with absolute
LSP position information for each token.
-/
def computeAbsoluteLspSemanticTokens
    (text     : FileMap)
    (beginPos : String.Pos.Raw)
    (endPos?  : Option String.Pos.Raw)
    (tokens   : Array LeanSemanticToken) :
    Array AbsoluteLspSemanticToken :=
  tokens.filterMap fun tok => do
    let ⟨pos, tailPos⟩ := tok.range
    guard <| beginPos <= pos && endPos?.all (pos < ·)
    -- Every token should be non-empty
    guard <| pos < tailPos
    return {
      pos := text.utf8PosToLspPos pos
      tailPos := text.utf8PosToLspPos tailPos
      type := tok.type
      priority := tok.priority
      modifiers := encodeModifiers tok.modifiers
    }

/--
The state used to handle computing non-overlapping semantic tokens. See
`handleOverlappingSemanticTokens` for a description of the problem.

Tokens are computed by iterating over every token _boundary_. At a given boundary, one of the
following things may happen:
1. We leave the range of a token, and there is no current token
2. We leave the range of a token, starting a new one
3. We start a token when there was none before

To do this, we maintain a set of tokens that could in principle occupy the interval from the last
token boundary to the one being considered. This includes tokens that are already in progress, and
potentially a new one from the input. The one with the highest priority is selected to be the next
one at each transition.
-/
private structure HandleOverlapState where
  /-- The non-overlapping tokens that have been definitively produced -/
  nonOverlapping : Array AbsoluteLspSemanticToken
  /--
  The current interval's token, with its start position suitably adjusted. The current interval's
  token always has a priority that's at least as high as all tokens in `surrounding` (they may be
  equal if overlapping tokens had the same priority, and a tiebreaker such as length was used).

  When a token is replaced by a higher-priority token in part of its interval, its start position is
  set to the end position of the overriding token when it is resumed.
  -/
  current? : Option AbsoluteLspSemanticToken
  /--
  The other tokens whose intervals include the current token's start position.

  Sorted by end position (increasing), because we've already passed their start positions. Only
  their end positions may contribute new token boundaries.
  -/
  surrounding : List AbsoluteLspSemanticToken
deriving Inhabited

/--
Adds a surrounding token to the set. These are tokens whose interval includes the boundaries being
processed, but are superseded by the current token.
-/
private def HandleOverlapState.insertSurrounding
    (st : HandleOverlapState) (s : AbsoluteLspSemanticToken) : HandleOverlapState :=
  { st with surrounding := go st.surrounding }
where
  go
    | [] => [s]
    | x :: xs =>
      if s.tailPos < x.tailPos then s :: x :: xs else x :: go xs

/--
Handles state transitions that are not due to a new token. If `nextToken?` is `none`, then there are
no more tokens to process, so all remaining transitions occur. If it is `some t`, then state
transitions only occur for token boundaries less than the `t`'s start.
-/
private def HandleOverlapState.untilToken (st : HandleOverlapState) (nextToken? : Option AbsoluteLspSemanticToken) : HandleOverlapState := Id.run do
  let mut st := st
  repeat
    if let some curr := st.current? then
      -- We know that the current token is higher priority (modulo tiebreaking criteria) than
      -- surrounding tokens, so we should discard any surrounding tokens that end before it does.
      -- This ensures that the surrounding tokens always end strictly later than the current token.
      st := { st with surrounding := st.surrounding.dropWhile (·.tailPos ≤ curr.tailPos) }
      -- If the current token ends before the next token starts, or if there are no new tokens, then
      -- we end it now
      let endNow : Bool :=
        if let some t := nextToken? then curr.tailPos ≤ t.pos else true
      if endNow then
        st := { st with
          nonOverlapping := st.nonOverlapping.push curr,
          -- Because all surrounding tokens end later than the current token, the new current token
          -- is non-empty.
          current? := takeBest st.surrounding |>.map ({ · with pos := curr.tailPos })
        }
      -- If the current token extends past the start of the next token,
      -- then all remaining surrounding tokens also extend past the start of the next token,
      -- which are all lower priority than the current token.
      -- Hence, we are ready to handle the next token.
      else
        break
    else
      -- Check whether the surrounding tokens need to become current.
      -- Make the highest-priority surrounding token into the new current one.
      if let some best := takeBest st.surrounding then
        -- No need to remove it from surrounding because this will happen at its end position
        st := { st with current? := best }
      else
        -- Nothing is current, and nothing is surrounding. We're done.
        break
  st
where
  /--
  The best token is the nonempty token with the highest priority; given equal priorities, earlier
  tokens win. Breaking ties in favor of shorter tokens means that more information has the chance to
  be displayed.
  -/
  takeBest (toks : List AbsoluteLspSemanticToken) : Option AbsoluteLspSemanticToken :=
    toks.foldl (init := none) fun
      | none, t =>
        some t
      | some soFar, t =>
        if better t soFar then
          some t
        else
          some soFar

  better (t soFar : AbsoluteLspSemanticToken) : Bool :=
    (t.priority > soFar.priority || (t.priority == soFar.priority && t.tailPos < soFar.tailPos))

/--
Handles a new token. First, `untilToken` is called, which takes care of all transitions that are due
to token boundaries prior to the start of `t`. After that `t`'s priority is compared to the current
token (if any), and then the highest-priority of the two is made current with the other relegated to
the surrounding tokens list. If `t` and the current token have the same priority, then the one that
starts later or ends earlier is made into the new current token.
-/
private def HandleOverlapState.token (st : HandleOverlapState) (t : AbsoluteLspSemanticToken) : HandleOverlapState := Id.run do
  let st := st.untilToken (some t)
  -- Now we know that the current token, if present, overlaps with `t`
  let some curr := st.current?
    | -- If there was no current token, then there's no surrounding tokens either
      return { st with current? := some t }
  if curr.priority > t.priority then
    -- Insert t into surrounding, continue with current
    return st.insertSurrounding t
  -- Tied priorities: make the token that starts later or ends earlier current.
  if curr.priority == t.priority then
    if curr.pos == t.pos then -- if `t` starts later, transition to it. Same start, keep the one that ends first.
      if curr.tailPos < t.tailPos then
        return st.insertSurrounding t

  -- Transition to t, save current if it's longer than t
  let st := { st with
    current? := some t,
    nonOverlapping :=
      let curr := { curr with tailPos := t.pos }
      -- Only save the token if it actually takes up space. This step is what filters out
      -- actual duplicates.
      if curr.pos < curr.tailPos then
        st.nonOverlapping.push curr
      else
        st.nonOverlapping
  }
  if curr.tailPos > t.tailPos then
    return st.insertSurrounding curr
  else
    return st



/--
Eliminates overlapping tokens by selecting a single “best” token for each interval between token
boundaries.

While LSP allows clients to state they they can handle overlapping tokens, widely used clients such
as VS Code cannot handle them. Thus, we need to make them non-overlapping (this strictly generalizes
removal of duplicates).

Given tokens A, B, C, D as in:
```
|-----A------|  |----D----|
    |------B----------|
        |----C----|
```
with priorities C > B, B > A, B > D, we want to emit the tokens:
```
|-A-|-B-|----C----|-B-|-D--|
```
In other words, `B` is split into two regions: before and after `C`.

If two overlapping tokens have the same priority, then ties are broken as follows:
 * If the tokens start at the same position, then the shorter one is used.
 * If they have the same start position and are the same length, then the one that occurs later in
   the original input array is used.
 * If a new token starts in the middle of an existing one, and they have the same priority, then the
   new token is used.

Callers should ensure that all tokens in `tokens` designate non-empty regions of the file. In other
words, it should be true that `∀ t ∈ tokens, t.pos < t.tailPos`.
-/
def handleOverlappingSemanticTokens (tokens : Array AbsoluteLspSemanticToken) :
    Array AbsoluteLspSemanticToken := Id.run do
  -- The sort must be stable so that the final tiebreaker is position in the input array.
  let count := tokens.size
  let tokens := tokens.toList.mergeSort fun ⟨pos1, tailPos1, _, _, _⟩ ⟨pos2, tailPos2, _, _, _⟩ =>
    pos1 < pos2 || pos1 == pos2 && tailPos1 ≤ tailPos2
  let mut st : HandleOverlapState := {
    current? := none
    -- Reserve 10% for overlaps
    nonOverlapping := Array.mkEmpty ((count * 11) / 10)
    surrounding := []
  }
  for t in tokens do
    st := st.token t
  st := st.untilToken none
  return st.nonOverlapping


/--
Given a set of `AbsoluteLspSemanticToken`, computes the LSP `SemanticTokens` data with
token-relative positioning.
See https://microsoft.github.io/language-server-protocol/specifications/lsp/3.17/specification/#textDocument_semanticTokens.
-/
def computeDeltaLspSemanticTokens (tokens : Array AbsoluteLspSemanticToken) : SemanticTokens := Id.run do
  let tokens := tokens.qsort fun ⟨pos1, tailPos1, _, _, _⟩ ⟨pos2, tailPos2, _, _, _⟩ =>
    pos1 < pos2 || pos1 == pos2 && tailPos1 <= tailPos2
  let mut data : Array Nat := Array.mkEmpty (5*tokens.size)
  let mut lastPos : Lsp.Position := ⟨0, 0⟩
  for ⟨pos, tailPos, tokenType, _, tokenModifiers⟩ in tokens do
    let deltaLine := pos.line - lastPos.line
    let deltaStart := pos.character - (if pos.line == lastPos.line then lastPos.character else 0)
    let length := tailPos.character - pos.character
    let tokenType := tokenType.toNat
    data := data ++ #[deltaLine, deltaStart, length, tokenType, tokenModifiers]
    lastPos := pos
  return { data }

/-!
## Markdown highlighting

Traverses the result of the full Markdown parse (`Lean.Markdown.parseDocument`,
which runs both passes) and emits `LeanSemanticToken`s.
-/

namespace MarkupTokens

variable {s : String.Slice}

/-- The kind of the innermost heading, blockquote, or list item that contains a piece of text. -/
private inductive MarkupBlockCtxt where
  | none
  | heading
  | quote
  | list

/--
The formatting that applies to a piece of text: whether it is inside bold emphasis, whether it is
inside italic emphasis, and the innermost heading, blockquote, or list item that contains it. The
block context determines the token type of the text, and the emphasis its modifiers.
-/
private structure MarkupAttrs where
  bold   : Bool := false
  italic : Bool := false
  block  : MarkupBlockCtxt := .none

@[inline] private def MarkupAttrs.withBold (a : MarkupAttrs) : MarkupAttrs :=
  { a with bold := true }

@[inline] private def MarkupAttrs.withItalic (a : MarkupAttrs) : MarkupAttrs :=
  { a with italic := true }

@[inline] private def MarkupAttrs.withBlock (a : MarkupAttrs) (b : MarkupBlockCtxt) : MarkupAttrs :=
  { a with block := b }

/-- The token type of text with these attributes. -/
private def MarkupAttrs.tokenType (a : MarkupAttrs) : SemanticTokenType :=
  match a.block with
  | .none => .markupDocText
  | .heading => .markupHeading
  | .quote => .markupQuote
  | .list => .markupList

/-- The token modifiers of text with these attributes. -/
private def MarkupAttrs.modifiers (a : MarkupAttrs) : List SemanticTokenModifier :=
  (if a.bold then [.markupBold] else []) ++ (if a.italic then [.markupItalic] else [])

/--
The raw source range of `sub` in the underlying string, which the LSP layer converts to positions.
-/
@[inline] private def toSyntaxRange (sub : s.Subslice) : Syntax.Range :=
  ⟨sub.startInclusive.str.offset, sub.endExclusive.str.offset⟩

/--
Pushes a `LeanSemanticToken` for `sub`, which is on a single source line. Does nothing when `sub` is
empty.
-/
@[inline] private def pushTok (out : Array LeanSemanticToken) (sub : s.Subslice)
    (tokenType : SemanticTokenType) (priority : Nat := 5)
    (modifiers : List SemanticTokenModifier := []) : Array LeanSemanticToken :=
  if sub.toSlice.isEmpty then out
  else out.push { range := toSyntaxRange sub, type := tokenType, priority, modifiers }

/-- Pushes one `LeanSemanticToken` per line in `lines`. -/
private def pushLines (out : Array LeanSemanticToken) (lines : Markdown.Lines s)
    (tokenType : SemanticTokenType) (priority : Nat := 5) : Array LeanSemanticToken :=
  lines.toArray.foldl (init := out) fun out line => pushTok out line tokenType priority

/-- Pushes a delimiter: a `keyword` token with the `markupSyntax` modifier. -/
@[inline] private def pushDelimiter (out : Array LeanSemanticToken) (delimiter : s.Subslice) :
    Array LeanSemanticToken :=
  pushTok out delimiter .keyword (modifiers := [.markupSyntax])

/-- Pushes text with the type and modifiers of the attributes `a`. -/
@[inline] private def pushText (out : Array LeanSemanticToken) (text : s.Subslice)
    (a : MarkupAttrs) : Array LeanSemanticToken :=
  pushTok out text a.tokenType (priority := 4) (modifiers := a.modifiers)

/-- Emits a destination: keyword on its angle brackets, if any, and URL on the URL. -/
private def emitDestination (out : Array LeanSemanticToken) (d : Markdown.LinkDestination s) :
    Array LeanSemanticToken := Id.run do
  let mut out := out
  if let some (o, c) := d.angles? then
    out := pushDelimiter out o
    out := pushDelimiter out c
  out := pushTok out d.url .markupUrl
  return out

private partial def emitInlines (a : MarkupAttrs)
    (inlines : Array (Markdown.Inline s)) (out : Array LeanSemanticToken) :
    Array LeanSemanticToken := Id.run do
  let mut out := out
  for i in inlines do
    out := emitInline a i out
  return out
where
  emitInline (a : MarkupAttrs) (i : Markdown.Inline s)
      (out : Array LeanSemanticToken) : Array LeanSemanticToken := Id.run do
    let mut out := out
    match i with
    | .text r =>
      out := pushText out r a
    | .softBreak _ => pure ()
    | .escape backslash char =>
      out := pushDelimiter out backslash
      out := pushText out char a
    | .entity r _ =>
      out := pushText out r a
    | .code openTicks content closeTicks =>
      out := pushDelimiter out openTicks
      out := pushDelimiter out closeTicks
      out := pushLines out content.lines .markupInlineCode (priority := 6)
    | .italic openDelim content closeDelim =>
      out := pushDelimiter out openDelim
      out := pushDelimiter out closeDelim
      out := emitInlines a.withItalic content out
    | .bold openDelim content closeDelim =>
      out := pushDelimiter out openDelim
      out := pushDelimiter out closeDelim
      out := emitInlines a.withBold content out
    | .link openBracket inner closeBracket target =>
      out := emitBracketed none openBracket inner closeBracket target out
    | .image bang openBracket alt closeBracket target =>
      out := emitBracketed (some bang) openBracket alt closeBracket target out
    | .hardBreak marker _ =>
      out := pushDelimiter out marker
    | .autolink openAngle url closeAngle _ =>
      out := pushDelimiter out openAngle
      out := pushDelimiter out closeAngle
      out := pushTok out url .markupUrl
    | .html lines =>
      out := pushLines out lines .markupInlineCode (priority := 6)
    return out

  /--
  Emits the tokens of a reference-style link's label and second bracket pair, if any.

  The label gets one `markupCrossReference` token per line. In full form, the link's text is emitted
  as ordinary inlines and the label is the interior of the second brackets. In collapsed and
  shortcut form, the link's text *is* the label. The second brackets are delimiters.
  -/
  emitReferenceForm (a : MarkupAttrs) (out : Array LeanSemanticToken)
      (inner : Array (Markdown.Inline s)) (label : Markdown.Lines s)
      (form : Markdown.ReferenceLinkForm s) : Array LeanSemanticToken := Id.run do
    let mut out := out
    match form with
    | .full openB closeB =>
      out := emitInlines a inner out
      out := pushDelimiter out openB
      out := pushDelimiter out closeB
    | .collapsed openB closeB =>
      out := pushDelimiter out openB
      out := pushDelimiter out closeB
    | .shortcut => pure ()
    out := pushLines out label .markupCrossReference (priority := 6)
    return out

  /--
  Emits the tokens shared by `[…]…` links and `![…]…` images.
  -/
  emitBracketed (bang? : Option (s.Subslice))
      (openBracket : s.Subslice) (inner : Array (Markdown.Inline s))
      (closeBracket : s.Subslice) (target : Markdown.LinkTarget s)
      (out : Array LeanSemanticToken) : Array LeanSemanticToken := Id.run do
    let mut out := out
    if let some bang := bang? then
      out := pushDelimiter out bang
    out := pushDelimiter out openBracket
    out := pushDelimiter out closeBracket
    match target with
    | .inline openParen destination closeParen title? =>
      out := emitInlines a inner out
      out := pushDelimiter out openParen
      out := emitDestination out destination
      if let some t := title? then
        out := pushDelimiter out t.opener
        out := pushLines out t.content .string
        out := pushDelimiter out t.closer
      out := pushDelimiter out closeParen
    | .reference _ label form =>
      out := emitReferenceForm a out inner label form
    return out

/--
Emits the structural tokens of a matched link reference definition: keyword on the brackets and
colon and the optional title's delimiters, cross-reference on the label, URL on the destination, and
string on the title's text. The label and the title get one token per source line.
-/
private def emitRefDef (out : Array LeanSemanticToken) (r : Markdown.RefDef s) :
    Array LeanSemanticToken := Id.run do
  let mut out := out
  out := pushDelimiter out r.openBracket
  out := pushLines out r.label .markupCrossReference
  out := pushDelimiter out r.closeBracket
  out := pushDelimiter out r.colon
  out := emitDestination out r.destination
  if let some t := r.title? then
    out := pushDelimiter out t.opener
    out := pushLines out t.content .string
    out := pushDelimiter out t.closer
  return out

private partial def emitBlocks (a : MarkupAttrs) (blocks : Array (Markdown.Block s))
    (out : Array LeanSemanticToken) : Array LeanSemanticToken := Id.run do
  let mut out := out
  for b in blocks do
    out := emitBlock a b out
  return out
where
  emitBlock (a : MarkupAttrs) (b : Markdown.Block s)
      (out : Array LeanSemanticToken) : Array LeanSemanticToken := Id.run do
    let mut out := out
    match b with
    | .paragraph content =>
      out := emitInlines a content out
    | .atxHeading _ hashes content closeHashes? =>
      out := pushDelimiter out hashes
      if let some c := closeHashes? then out := pushDelimiter out c
      out := emitInlines (a.withBlock .heading) content out
    | .setextHeading _ content underline =>
      out := emitInlines (a.withBlock .heading) content out
      out := pushDelimiter out underline
    | .fencedCode info openFence closeFence? lines =>
      out := pushDelimiter out openFence
      if let some c := closeFence? then out := pushDelimiter out c
      if let some tag := info.infoString? then
        out := pushTok out tag .function
      for line in lines do
        out := pushTok out line.source .markupCodeBlock
    | .indentedCode lines | .html lines =>
      for line in lines do
        out := pushTok out line.source .markupCodeBlock
    | .blockquote markers children =>
      for m in markers do
        out := pushDelimiter out m
      out := emitBlocks (a.withBlock .quote) children out
    | .list _ _ items =>
      out := emitBlocks (a.withBlock .list) items out
    | .listItem marker children =>
      out := pushDelimiter out marker
      out := emitBlocks (a.withBlock .list) children out
    | .linkRefDef m =>
      out := emitRefDef out m
    | .thematicBreak line =>
      out := pushDelimiter out line
    return out

end MarkupTokens

/--
Collects semantic tokens for a Markdown docstring. Delimiters (`#`, `>`, list markers, fences,
brackets) are `keyword` tokens with the `markupSyntax` modifier; URLs are `markupUrl`; code block
contents are `markupCodeBlock`; and text is `markupDocText`, `markupHeading`, `markupQuote`, or
`markupList` by its block context, with the `markupBold` and `markupItalic` modifiers for emphasis.
-/
def collectMarkdownTokens (text : FileMap) (startPos endPos : String.Pos.Raw) (indent : Nat := 0) :
    Array LeanSemanticToken :=
  let whole := text.source.toSlice
  match whole.pos? startPos, whole.pos? endPos with
  | some start, some stop =>
    if h : start ≤ stop then
      MarkupTokens.emitBlocks {} (Markdown.parseDocument (whole.slice start stop h) indent) #[]
    else #[]
  | _, _ => #[]

open Lean.Doc MarkupTokens in
private partial def collectVersoTokens
    (stx : Syntax) (getTokens : (stx : Syntax) → Array LeanSemanticToken) :
    Array LeanSemanticToken :=
  go {} stx |>.run #[] |>.2
where
  tok (tk : Syntax) (k : SemanticTokenType) (modifiers : List SemanticTokenModifier := []) :
      StateM (Array LeanSemanticToken) Unit :=
    let priority :=
      match k with
      -- Code tokens are the default highlighting of code element contents. They should be
      -- overridden by anything more specific, like variable names, that occurs in these elements,
      -- so they get a lower priority.
      | .markupInlineCode | .markupCodeBlock => 3
      | _ => 5
    modify (pushSyntaxToken · tk k priority modifiers)

  /-- Emits a delimiter: a `keyword` token with the `markupSyntax` modifier. -/
  delim (tk : Syntax) : StateM (Array LeanSemanticToken) Unit :=
    tok tk .keyword [.markupSyntax]

  /--
  The region of a code block line to highlight. The line's final newline is omitted because some LSP
  clients (including VS Code) ignore a token that spans a line break.
  -/
  codeLine (line : Syntax) (value : String) : Option Syntax := do
    let ⟨pos, tailPos⟩ ← line.getRange?
    let tailPos := if value.endsWith "\n" then tailPos - '\n' else tailPos
    return .ofRange ⟨pos, tailPos⟩

  goArg (arg : TSyntax ``Parser.arg) :
      StateM (Array LeanSemanticToken) Unit := do
    match ArgView.of arg with
    | some (.named _ parens x tk v) =>
      if let some (o, _) := parens then delim o
      tok x.raw .property
      delim tk
      tok v.raw .parameter
      if let some (_, c) := parens then delim c
    | some (.flag _ tk x _) =>
      delim tk
      tok x.raw .property
    | some (.anon _ v) => tok v.raw .parameter
    | none => pure ()

  goTarget (tgt : LinkTargetView) : StateM (Array LeanSemanticToken) Unit := do
    match tgt with
    | .ref _ tk1 name tk2 =>
      delim tk1
      tok name.raw .markupCrossReference
      delim tk2
    | .url _ tk1 url tk2 =>
      delim tk1
      tok url.raw .markupUrl
      delim tk2

  goCode (code : CodeView) : StateM (Array LeanSemanticToken) Unit := do
    delim code.opener
    for line in code.content.getVersoCodeLines do
      if let some region := codeLine line.raw line.getVersoCodeLine then tok region .markupInlineCode
    delim code.closer

  goItem (a : MarkupAttrs) (marker : Syntax) (contents : TSyntaxArray ``Parser.block) :
      StateM (Array LeanSemanticToken) Unit := do
    delim marker
    for b in contents do go a b.raw

  goDelimited (a : MarkupAttrs) (opener closer : Syntax) (content : TSyntaxArray ``Parser.inline) :
      StateM (Array LeanSemanticToken) Unit := do
    delim opener
    for i in content do go a i.raw
    delim closer

  goDesc (a : MarkupAttrs) (item : DescItemView) : StateM (Array LeanSemanticToken) Unit := do
    delim item.marker
    for i in item.term do go a i.raw
    for b in item.desc do go a b.raw

  go (a : MarkupAttrs) (stx : Syntax) : StateM (Array LeanSemanticToken) Unit := do
  if let some v := InlineView.of ⟨stx⟩ then
    match v with
    | .text v => tok v.stx.raw a.tokenType a.modifiers
    | .linebreak .. => pure ()
    | .bold v => goDelimited a.withBold v.opener v.closer v.content
    | .emph v => goDelimited a.withItalic v.opener v.closer v.content
    | .link v =>
      goDelimited a v.opener v.closer v.content
      goTarget v.target
    | .image v =>
      delim v.opener
      tok v.alt.raw .string
      delim v.closer
      goTarget v.target
    | .footnote v =>
      delim v.opener
      tok v.name.raw .markupCrossReference
      delim v.closer
    | .code v =>
      goCode v
    | .role v =>
      delim v.braceOpen
      tok v.name.raw .function
      for arg in v.args do goArg arg
      delim v.braceClose
      if let some (o, _) := v.brackets then delim o
      for i in v.content do go a i.raw
      if let some (_, c) := v.brackets then delim c
    | .math v =>
      delim v.marker
      goCode v.code
  else if let some v := BlockView.of ⟨stx⟩ then
    match v with
    | .para v =>
      for i in v.content do go a i.raw
    | .codeblock v =>
      delim v.openFence
      if let some x := v.name? then
        tok x.raw .function
        for arg in v.args do goArg arg
      for line in v.content.getVersoCodeBlockLines do
        if let some region := codeLine line.raw line.getVersoCodeLine then tok region .markupCodeBlock
      delim v.closeFence
    | .directive v =>
      delim v.opener
      tok v.name.raw .function
      for arg in v.args do goArg arg
      for b in v.content do go a b.raw
      delim v.closer
    | .command v =>
      delim v.braceOpen
      tok v.name.raw .function
      for arg in v.args do goArg arg
      delim v.braceClose
    | .metadata v =>
      delim v.opener
      modify (· ++ getTokens v.contents.raw)
      delim v.closer
    | .linkRef v =>
      delim v.opener
      tok v.name.raw .markupCrossReference
      delim v.closer
      tok v.url.raw .markupUrl
    | .footnoteRef v =>
      delim v.opener
      tok v.name.raw .markupCrossReference
      delim v.closer
      for i in v.content do go a i.raw
    | .header v =>
      delim v.marker
      for i in v.content do go (a.withBlock .heading) i.raw
    | .ul v =>
      for item in v.items do goItem (a.withBlock .list) item.marker item.contents
    | .ol v =>
      for item in v.items do goItem (a.withBlock .list) item.marker item.contents
    | .dl v =>
      for item in v.items do goDesc (a.withBlock .list) item
    | .blockquote v =>
      delim v.marker
      for b in v.content do go (a.withBlock .quote) b.raw
  else
    stx.getArgs.forM (go a)

/--
Collects all semantic tokens that can be deduced purely from `Syntax`
without elaboration information.
-/
partial def collectSyntaxBasedSemanticTokens (text : FileMap) : (stx : Syntax) → Array LeanSemanticToken
  | `($e.$id:ident)    =>
    let tokens := collectSyntaxBasedSemanticTokens text e
    pushSyntaxToken tokens id .property
  | `($e |>.$field:ident) =>
    let tokens := collectSyntaxBasedSemanticTokens text e
    pushSyntaxToken tokens field .property
  | stx => Id.run do
    if noHighlightKinds.contains stx.getKind then
      return #[]
    if docKinds.contains stx.getKind then
      if stx[1].isOfKind ``Lean.Parser.Command.versoCommentBody then
        return collectVersoTokens stx[1] (collectSyntaxBasedSemanticTokens text)
      else if stx[1].isOfKind ``Lean.Parser.Command.commentBody then
        -- The text atom's range excludes the closing delimiter and the whitespace before it.
        let some ⟨startPos, endPos⟩ := stx[1][0].getRange?
          | return #[]
        let some openPos := stx[0].getPos? | return #[]
        let some closerPos := stx[1][1].getPos? | return #[]
        -- The docstring's indentation is its base column, determined as for Verso docstrings.
        let indent := Doc.Parser.docStringBaseColumn text openPos startPos closerPos
        return collectMarkdownTokens text startPos endPos indent
      else
        return #[]
    let mut tokens :=
      if stx.isOfKind choiceKind then
        collectSyntaxBasedSemanticTokens text stx[0]
      else
        stx.getArgs.map (collectSyntaxBasedSemanticTokens text) |>.flatten
    let Syntax.atom _ val := stx
      | return tokens
    let isRegularKeyword := val.front?.any isIdFirst
    let isHashKeyword := ((val.dropPrefix? '#').bind (·.front?)).any isIdFirst
    if ! isRegularKeyword && ! isHashKeyword then
      return tokens
    return pushSyntaxToken tokens stx (keywordSemanticTokenMap.getD val .keyword)

/-- Collects all semantic tokens from the given `Elab.InfoTree`. -/
def collectInfoBasedSemanticTokens (i : Elab.InfoTree) : Array LeanSemanticToken :=
  List.toArray <| i.deepestNodes fun _ info _ => do
    let .ofTermInfo ti := info
      | none
    let .original .. := ti.stx.getHeadInfo
      | none
    if let `($_:ident) := ti.stx then
      if let Expr.fvar fvarId .. := ti.expr then
        if let some localDecl := ti.lctx.find? fvarId then
          -- Recall that `isAuxDecl` is an auxiliary declaration used to elaborate a recursive definition.
          if localDecl.isAuxDecl then
            if ti.isBinder then
              return (← LeanSemanticToken.ofSyntax? ti.stx .function)
          else if ! localDecl.isImplementationDetail then
            return (← LeanSemanticToken.ofSyntax? ti.stx .variable)
    if ti.stx.getKind == Parser.Term.identProjKind then
      return (← LeanSemanticToken.ofSyntax? ti.stx .property)
    none

/--
A debugging utility for inspecting sets of collected tokens, classified by line and sorted by
column.
-/
def dbgShowTokens (text : FileMap) (toks : Array LeanSemanticToken) : String := Id.run do
  let mut byLine : Std.HashMap Nat (Array (Nat × Nat × LeanSemanticToken)) := {}
  for tok in toks do
    let ⟨l, c1⟩ := text.utf8PosToLspPos tok.range.start
    let ⟨_, c2⟩ := text.utf8PosToLspPos tok.range.stop
    byLine := byLine.alter l fun x? => some (x?.getD #[] |>.push (c1, c2, tok))
  let mut out := ""
  for (l, vals) in byLine.toList.mergeSort (fun x y => x.1 ≤ y.1) do
    let vals := vals.toList.mergeSort fun x y => x.1 ≤ y.1
    out := out ++ s!"{l}:\t{vals.map (fun (c1, c2, tok) => (c1, c2, toJson tok.type, tok.priority, tok.modifiers.map toJson))}\n"
  out

def computeSemanticTokens  (doc : EditableDocument) (beginPos : String.Pos.Raw)
    (endPos? : Option String.Pos.Raw) (snaps : List Snapshots.Snapshot) : RequestM SemanticTokens := do
  let mut leanSemanticTokens := #[]
  for s in snaps do
    if s.endPos <= beginPos then
      continue
    let syntaxBasedSemanticTokens := collectSyntaxBasedSemanticTokens doc.meta.text s.stx
    let infoBasedSemanticTokens := collectInfoBasedSemanticTokens s.infoTree
    leanSemanticTokens := leanSemanticTokens ++ syntaxBasedSemanticTokens ++ infoBasedSemanticTokens
    RequestM.checkCancelled
  let absoluteLspSemanticTokens := computeAbsoluteLspSemanticTokens doc.meta.text beginPos endPos? leanSemanticTokens
  RequestM.checkCancelled
  let absoluteLspSemanticTokens := handleOverlappingSemanticTokens absoluteLspSemanticTokens
  RequestM.checkCancelled
  let semanticTokens := computeDeltaLspSemanticTokens absoluteLspSemanticTokens
  return semanticTokens

structure SemanticTokensState where
  deriving TypeName, Inhabited

/-- Computes all semantic tokens for the document. -/
def handleSemanticTokensFull (_ : SemanticTokensParams) (_ : SemanticTokensState) :
    RequestM (LspResponse SemanticTokens × SemanticTokensState) := do
  let ctx ← read
  let doc ← readDoc
  -- Only grabs the finished prefix so that we do not need to wait for elaboration to complete
  -- for the full file before sending a response. This means that the response will be incomplete,
  -- which we mitigate by regularly sending `workspace/semanticTokens/refresh` requests in the
  -- `FileWorker` to tell the client to re-compute the semantic tokens.
  let (snaps, _, isComplete) ← doc.cmdSnaps.getFinishedPrefixWithTimeout 3000 (cancelTks := ctx.cancelTk.cancellationTasks)
  let response ← computeSemanticTokens doc 0 none snaps
  return ({ response, isComplete }, ⟨⟩)

def handleSemanticTokensDidChange (_ : DidChangeTextDocumentParams) :
    StateT SemanticTokensState RequestM Unit := do
  return

/-- Computes the semantic tokens in the range provided by `p`. -/
def handleSemanticTokensRange (p : SemanticTokensRangeParams) :
    RequestM (RequestTask SemanticTokens) := do
  let doc ← readDoc
  let text := doc.meta.text
  let beginPos := text.lspPosToUtf8Pos p.range.start
  let endPos := text.lspPosToUtf8Pos p.range.end
  let t := doc.cmdSnaps.waitUntil (·.endPos >= endPos)
  mapTaskCostly t fun (snaps, _) =>
    computeSemanticTokens doc beginPos endPos snaps

builtin_initialize
  registerLspRequestHandler
    "textDocument/semanticTokens/range"
    SemanticTokensRangeParams
    SemanticTokens
    handleSemanticTokensRange
  registerPartialStatefulLspRequestHandler
    "textDocument/semanticTokens/full"
    "workspace/semanticTokens/refresh"
    2000
    SemanticTokensParams
    SemanticTokens
    SemanticTokensState
    ⟨⟩
    handleSemanticTokensFull
    handleSemanticTokensDidChange

end Lean.Server.FileWorker
