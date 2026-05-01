/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich, Marc Huisinga
-/
module

prelude
public import Lean.Server.Requests
public import Lean.Server.FileWorker.Markdown

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

/-- Semantic token information for a given `Syntax`. -/
structure LeanSemanticToken where
  /-- Syntax of the semantic token. -/
  stx  : Syntax
  /-- Type of the semantic token. -/
  type : SemanticTokenType
  /-- In case of overlap, higher-priority tokens will take precedence -/
  priority : Nat := 5

/-- Semantic token information with absolute LSP positions. -/
structure AbsoluteLspSemanticToken where
  /-- Start position of the semantic token. -/
  pos     : Lsp.Position
  /-- End position of the semantic token. -/
  tailPos : Lsp.Position
  /-- Start position of the semantic token. -/
  type    : SemanticTokenType
  /-- In case of overlap, higher-priority tokens will take precedence -/
  priority : Nat := 5
  deriving BEq, Hashable, FromJson, ToJson

/--
Given a set of `LeanSemanticToken`, computes the `AbsoluteLspSemanticToken` with absolute
LSP position information for each token.
-/
def computeAbsoluteLspSemanticTokens
    (text     : FileMap)
    (beginPos : String.Pos.Raw)
    (endPos?  : Option String.Pos.Raw)
    (tokens   : Array LeanSemanticToken)
    : Array AbsoluteLspSemanticToken :=
  tokens.filterMap fun tok => do
    let (pos, tailPos) := (← tok.stx.getPos?, ← tok.stx.getTailPos?)
    guard <| beginPos <= pos && endPos?.all (pos < ·)
    let (lspPos, lspTailPos) := (text.utf8PosToLspPos pos, text.utf8PosToLspPos tailPos)
    return { tok with pos := lspPos, tailPos := lspTailPos }

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
  -- `insertionSort` is used because a stable sort is needed here in order to allow the final
  -- tiebreaker to be position in the input array
  let count := tokens.size
  let tokens := tokens.toList.mergeSort fun ⟨pos1, tailPos1, _, _⟩ ⟨pos2, tailPos2, _, _⟩ =>
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
  let tokens := tokens.qsort fun ⟨pos1, tailPos1, _, _⟩ ⟨pos2, tailPos2, _, _⟩ =>
    pos1 < pos2 || pos1 == pos2 && tailPos1 <= tailPos2
  let mut data : Array Nat := Array.mkEmpty (5*tokens.size)
  let mut lastPos : Lsp.Position := ⟨0, 0⟩
  for ⟨pos, tailPos, tokenType, _⟩ in tokens do
    let deltaLine := pos.line - lastPos.line
    let deltaStart := pos.character - (if pos.line == lastPos.line then lastPos.character else 0)
    let length := tailPos.character - pos.character
    let tokenType := tokenType.toNat
    let tokenModifiers := 0
    data := data ++ #[deltaLine, deltaStart, length, tokenType, tokenModifiers]
    lastPos := pos
  return { data }

open Lean.Doc.Syntax in
def isVersoKind (k : SyntaxNodeKind) : Bool :=
  (`Lean.Doc.Syntax).isPrefixOf k

/--
Split the token at newline boundaries to support LSP clients such as VS Code that can't deal with
newline-spanning tokens.
-/
private def splitStr (text : FileMap) (stx : Syntax) : Array Syntax := Id.run do
  let some ⟨pos, tailPos⟩ := stx.getRange?
    | return #[]
  -- Construct fake syntax with the right source spans
  let mut pos := pos
  let mut stxs := #[]
  -- Gets the line number of the syntax's position, to avoid iterating over lines that don't include
  -- the region of interest. As an index into `text.positions`, this line number is the index of
  -- the position of the _next_ line's start.
  let startLine := text.toPosition pos |>.line
  for h : i in [startLine:text.positions.size] do
    let l := text.positions[i]
    if l > tailPos then
      stxs := stxs.push <| Syntax.ofRange ⟨pos, tailPos⟩
      break
    -- Here, `l` is the position of the first character of the next line. This means that
    -- terminating the token at `l` includes the newline. If the semantic token includes the
    -- newline, then VS Code ignores it (it doesn't support multi-line tokens), so the token
    -- should be terminated one character earlier.
    let l' := l.prev text.source
    stxs := stxs.push <| .ofRange ⟨pos, l'⟩
    pos := l
  return stxs


/-! ## Markdown highlighting

Walks the result of the full Markdown parse (`Lean.Server.FileWorker.Markdown.parseDocument`,
which runs both passes) and emits `LeanSemanticToken`s. The walk is purely structural — no
inline parsing happens here; each `Block (Array Inline)` already carries its parsed inlines
with file-anchored positions.
-/

namespace Markdown

/-- Block context for combining markup highlighting types. -/
private inductive MarkupBlockCtxt where
  | none
  | heading
  | quote
  | list

/--
Active markup attributes during the walk: which emphasis is in scope and the
nearest enclosing block context. `markupTypeOf?` maps an attribute set to the
matching `SemanticTokenType` constructor (or `none` for plain text in plain
context, which is not emitted as a markup token).
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

private def markupTypeOf : MarkupAttrs → SemanticTokenType
  | { bold := false, italic := false, block := .none } => .markupDocText
  | { bold := true,  italic := false, block := .none } => .markupBold
  | { bold := false, italic := true,  block := .none } => .markupItalic
  | { bold := true,  italic := true,  block := .none } => .markupBoldItalic
  | { bold := false, italic := false, block := .heading } => .markupHeading
  | { bold := true,  italic := false, block := .heading } => .markupBoldHeading
  | { bold := false, italic := true,  block := .heading } => .markupItalicHeading
  | { bold := true,  italic := true,  block := .heading } => .markupBoldItalicHeading
  | { bold := false, italic := false, block := .quote } => .markupQuote
  | { bold := true,  italic := false, block := .quote } => .markupBoldQuote
  | { bold := false, italic := true,  block := .quote } => .markupItalicQuote
  | { bold := true,  italic := true,  block := .quote } => .markupBoldItalicQuote
  | { bold := false, italic := false, block := .list } => .markupList
  | { bold := true,  italic := false, block := .list } => .markupBoldList
  | { bold := false, italic := true,  block := .list } => .markupItalicList
  | { bold := true,  italic := true,  block := .list } => .markupBoldItalicList

/--
Converts a `Syntax.Range` to a `Syntax` carrying the same source span.
The resulting syntax is suitable as a `LeanSemanticToken.stx`; the LSP layer
already handles raw byte offsets via `text.utf8PosToLspPos`.
-/
@[inline] private def srcRangeToSyntax (r : Syntax.Range) : Syntax :=
  Syntax.ofRange ⟨r.start, r.stop⟩

/--
Pushes one `LeanSemanticToken` per source line covered by `r`. Single-line ranges go through
unchanged; multi-line ranges (e.g. fenced code blocks) are split at newline boundaries.
-/
private def pushSplit (text : FileMap) (out : Array LeanSemanticToken)
    (r : Syntax.Range) (tokenType : SemanticTokenType) (priority : Nat := 5) :
    Array LeanSemanticToken := Id.run do
  if r.start == r.stop then return out
  let stx := srcRangeToSyntax r
  let mut out := out
  for line in splitStr text stx do
    out := out.push { stx := line, type := tokenType, priority }
  return out

/--
Pushes a single-line `LeanSemanticToken` directly without going through `splitStr`. The caller
guarantees `r` does not span a newline.
-/
@[inline] private def pushTok (out : Array LeanSemanticToken) (r : Syntax.Range)
    (tokenType : SemanticTokenType) (priority : Nat := 5) : Array LeanSemanticToken :=
  if r.start == r.stop then out
  else out.push { stx := srcRangeToSyntax r, type := tokenType, priority }

private partial def emitInlines (text : FileMap) (a : MarkupAttrs)
    (inlines : Array Markdown.Inline) (out : Array LeanSemanticToken) :
    Array LeanSemanticToken := Id.run do
  let mut out := out
  for i in inlines do
    out := emitInline text a i out
  return out
where
  emitInline (text : FileMap) (a : MarkupAttrs) (i : Markdown.Inline)
      (out : Array LeanSemanticToken) : Array LeanSemanticToken := Id.run do
    let mut out := out
    match i with
    | .text r =>
      -- A soft break emits a one-byte `.text` covering just the `\n`. The
      -- inline tree retains it so downstream consumers (e.g. an HTML
      -- renderer) can reproduce the line ending, but for LSP semantic
      -- tokens it would translate to a multi-line token, which VS Code
      -- doesn't support.
      let isNewlineOnly := r.start.byteIdx + 1 == r.stop.byteIdx
        && r.start.get text.source == '\n'
      unless isNewlineOnly do
        out := pushTok out r (markupTypeOf a) (priority := 4)
    | .code openTicks content closeTicks =>
      out := pushTok out openTicks .keyword
      out := pushTok out closeTicks .keyword
      out := pushSplit text out content .markupInlineCode (priority := 6)
    | .italic openDelim content closeDelim =>
      out := pushTok out openDelim .keyword
      out := pushTok out closeDelim .keyword
      out := emitInlines text a.withItalic content out
    | .bold openDelim content closeDelim =>
      out := pushTok out openDelim .keyword
      out := pushTok out closeDelim .keyword
      out := emitInlines text a.withBold content out
    | .link openBracket inner closeBracket target =>
      out := emitBracketed none openBracket inner closeBracket target out
    | .image bang openBracket alt closeBracket target =>
      out := emitBracketed (some bang) openBracket alt closeBracket target out
    | .hardBreak _ => pure ()
    | .autolink openAngle url closeAngle _ =>
      out := pushTok out openAngle .keyword
      out := pushTok out closeAngle .keyword
      out := pushTok out url .markupUrl
    return out

  /--
  Emits the structural tokens for a reference-style link's bracket pair(s).

  For full form, the link's text content is walked as ordinary inlines and the second `[label]`
  brackets get keyword/cross-ref tokens. For collapsed and shortcut form, the link text *is* the
  label, so `markupCrossReference` covers the bracket interior in place of the inline walk. In
  collapsed form, the empty `[]` is annotated as a keyword.
  -/
  emitReferenceForm (text : FileMap) (a : MarkupAttrs)
      (out : Array LeanSemanticToken) (interior : Syntax.Range)
      (inner : Array Markdown.Inline) (form : Markdown.ReferenceLinkForm) :
      Array LeanSemanticToken := Id.run do
    let mut out := out
    match form with
    | .full openB label closeB =>
      out := emitInlines text a inner out
      out := pushTok out openB .keyword
      out := pushTok out closeB .keyword
      out := pushTok out label .markupCrossReference (priority := 6)
    | .collapsed openB closeB =>
      out := pushTok out interior .markupCrossReference (priority := 6)
      out := pushTok out openB .keyword
      out := pushTok out closeB .keyword
    | .shortcut =>
      out := pushTok out interior .markupCrossReference (priority := 6)
    return out

  /--
  Emits the tokens shared by `[…]…` links and `![…]…` images.
  -/
  emitBracketed (bang? : Option Syntax.Range)
      (openBracket : Syntax.Range) (inner : Array Markdown.Inline)
      (closeBracket : Syntax.Range) (target : Markdown.LinkTarget)
      (out : Array LeanSemanticToken) : Array LeanSemanticToken := Id.run do
    let mut out := out
    if let some bang := bang? then
      out := pushTok out bang .keyword
    out := pushTok out openBracket .keyword
    out := pushTok out closeBracket .keyword
    let interior : Syntax.Range :=
      { start := openBracket.stop, stop := closeBracket.start }
    match target with
    | .inline openParen url closeParen title? =>
      out := emitInlines text a inner out
      out := pushTok out openParen .keyword
      out := pushTok out url .markupUrl
      if let some t := title? then out := pushTok out t .string
      out := pushTok out closeParen .keyword
    | .reference _ _ form =>
      out := emitReferenceForm text a out interior inner form
    return out

/--
Emits the structural tokens of a matched link reference definition: keyword on the brackets and
colon, cross-reference on the label, URL on the destination, and string on the optional title. The
label and title may span multiple source lines, so they are split at line boundaries.
-/
private def emitRefDef (text : FileMap) (out : Array LeanSemanticToken) (r : RefDef) :
    Array LeanSemanticToken := Id.run do
  let mut out := out
  out := pushTok out r.openBracket .keyword
  out := pushSplit text out r.label .markupCrossReference
  out := pushTok out r.closeBracket .keyword
  out := pushTok out r.colon .keyword
  out := pushTok out r.url .markupUrl
  if let some t := r.title? then
    out := pushSplit text out t .string
  return out

private partial def emitBlocks (text : FileMap) (a : MarkupAttrs)
    (blocks : Array (Markdown.Block (Array Markdown.Inline)))
    (out : Array LeanSemanticToken) : Array LeanSemanticToken := Id.run do
  let mut out := out
  for b in blocks do
    out := emitBlock text a b out
  return out
where
  emitBlock (text : FileMap) (a : MarkupAttrs)
      (b : Markdown.Block (Array Markdown.Inline))
      (out : Array LeanSemanticToken) : Array LeanSemanticToken := Id.run do
    let mut out := out
    match b with
    | .paragraph lines =>
      for inls in lines do
        out := emitInlines text a inls out
    | .atxHeading hashes content closeHashes? =>
      out := pushTok out hashes .keyword
      if let some c := closeHashes? then out := pushTok out c .keyword
      out := emitInlines text (a.withBlock .heading) content out
    | .setextHeading _ lines underline =>
      for inls in lines do
        out := emitInlines text (a.withBlock .heading) inls out
      out := pushTok out underline .keyword
    | .fencedCode info openFence closeFence? lines =>
      out := pushTok out openFence .keyword
      if let some c := closeFence? then out := pushTok out c .keyword
      if let some tag := info.infoString? then
        out := pushTok out tag .function
      for line in lines do
        out := pushSplit text out line .markupCodeBlock
    | .indentedCode lines =>
      for (range, _) in lines do
        out := pushTok out range .markupCodeBlock
    | .blockquote markers children =>
      for m in markers do
        out := pushTok out m .keyword
      out := emitBlocks text (a.withBlock .quote) children out
    | .list _ _ items =>
      out := emitBlocks text (a.withBlock .list) items out
    | .listItem marker children =>
      out := pushTok out marker .keyword
      out := emitBlocks text (a.withBlock .list) children out
    | .linkRefDef m =>
      out := emitRefDef text out m
    | .thematicBreak line =>
      out := pushTok out line .keyword
    return out

end Markdown

/--
Collects semantic tokens for a Markdown docstring. Block delimiters (`#`, `>`, list markers, fence
runs, brackets) are emitted as `.keyword`; URL targets as `.markupUrl`; code block contents as
`.markupCodeBlock`; and inline emphasis as the appropriate `markup*` type combined with the
enclosing block context. Undecorated text is emitted as `.markupDocText`.
-/
def collectMarkdownTokens (text : FileMap) (startPos endPos : String.Pos.Raw) :
    Array LeanSemanticToken :=
  Markdown.emitBlocks text {} (Markdown.parseDocument text.source startPos endPos) #[]

open Lean.Doc.Syntax Markdown in
private partial def collectVersoTokens
    (text : FileMap)
    (stx : Syntax) (getTokens : (stx : Syntax) → Array LeanSemanticToken) :
    Array LeanSemanticToken :=
  go {} stx |>.run #[] |>.2
where
  tok (tk : Syntax) (k : SemanticTokenType) : StateM (Array LeanSemanticToken) Unit :=
    let priority :=
      match k with
      -- String tokens occur as the default highlighting of code element contents. They should be
      -- overridden by anything more specific, like variable names, that occurs in these elements,
      -- so they get a lower priority.
      | .string => 3
      | _ => 5
    modify (·.push { stx := tk, type := k, priority })

  go (a : MarkupAttrs) (stx : Syntax) : StateM (Array LeanSemanticToken) Unit := do
  match stx with
  | `(arg_val| $x:ident )
  | `(arg_val| $x:str )
  | `(arg_val| $x:num ) =>
    tok x .parameter
  | `(named| (%$tk1 $x:ident :=%$tk2 $v:arg_val )%$tk3) =>
    tok tk1 .keyword
    tok x .property
    tok tk2 .keyword
    go a v
    tok tk3 .keyword
  | `(named_no_paren| $x:ident :=%$tk $v:arg_val ) =>
    tok x .property
    tok tk .keyword
    go a v
  | `(flag_on| +%$tk$x)  | `(flag_off| -%$tk$x) =>
    tok tk .keyword
    tok x .property
  | `(link_target| [%$tk1 $s ]%$tk2) =>
    tok tk1 .keyword
    tok s .property
    tok tk2 .keyword
  | `(link_target| (%$tk1 $s )%$tk2) =>
    tok tk1 .keyword
    tok s .string
    tok tk2 .keyword
  | `(inline|$s:str) => tok s (markupTypeOf a)
  | `(inline|line! $_) => pure () -- No token for line breaks
  | `(inline| *[%$tk1 $inls* ]%$tk2) =>
    tok tk1 .keyword
    inls.forM (go a.withBold)
    tok tk2 .keyword
  | `(inline|_[%$tk1 $inls* ]%$tk2) =>
    tok tk1 .keyword
    inls.forM (go a.withItalic)
    tok tk2 .keyword
  | `(inline| link[%$tk1 $inls* ]%$tk2 $ref) =>
    tok tk1 .keyword
    inls.forM (go a)
    tok tk2 .keyword
    go a ref
  | `(inline| image(%$tk1 $s )%$tk2 $ref) =>
    tok tk1 .keyword
    tok s .string
    tok tk2 .keyword
    go a ref
  | `(inline| footnote(%$tk1 $s )%$tk2) =>
    tok tk1 .keyword
    tok s .property
    tok tk2 .keyword
  | `(inline| code(%$tk1 $s )%$tk2) =>
    tok tk1 .keyword
    tok s .string
    tok tk2 .keyword
  | `(inline| role{%$tk1 $x $args* }%$tk2 [%$tk3 $inls* ]%$tk4) =>
    tok tk1 .keyword
    tok x .function
    args.forM (go a)
    tok tk2 .keyword
    tok tk3 .keyword
    inls.forM (go a)
    tok tk4 .keyword
  | `(inline| \math%$tk1 code(%$tk2 $s )%$tk3)
  | `(inline| \displaymath%$tk1 code(%$tk2 $s )%$tk3) =>
    tok tk1 .keyword
    tok s .string
    tok tk2 .keyword
    tok tk3 .keyword
  | `(list_item| *%$tk $inls*) =>
    tok tk .keyword
    inls.forM (go (a.withBlock .list))
  | `(desc| :%$tk $inls* => $blks*) =>
    tok tk .keyword
    inls.forM (go (a.withBlock .list))
    blks.forM (go (a.withBlock .list))
  | `(block|para[$inl*]) => inl.forM (go a)
  | `(block| ```%$tk1 $x $args* | $s ```%$tk2)=>
    tok tk1 .keyword
    tok x .function
    args.forM (go a)
    for line in splitStr text s do tok line .string
    tok tk2 .keyword
  | `(block| :::%$tk1 $x $args* { $blks* }%$tk2)=>
    tok tk1 .keyword
    tok x .function
    args.forM (go a)
    blks.forM (go a)
    tok tk2 .keyword
  | `(block| command{%$tk1 $x $args*}%$tk2)=>
    tok tk1 .keyword
    tok x .function
    args.forM (go a)
    tok tk2 .keyword
  | `(block| %%%%$tk1 $vals* %%%%$tk2)=>
    tok tk1 .keyword
    modify (· ++ getTokens (mkNullNode vals))
    tok tk2 .keyword
  | `(block| [%$tk1 $s ]:%$tk2 $url) =>
    tok tk1 .keyword
    tok s .property
    tok tk2 .keyword
    tok url .string
  | `(block| [^%$tk1 $s ]:%$tk2 $inls*) =>
    tok tk1 .keyword
    tok s .property
    tok tk2 .keyword
    inls.forM (go a)
  | `(block| header(%$tk $_ ){ $inls* })=>
    tok tk .keyword
    inls.forM (go (a.withBlock .heading))
  | `(block| >%$tk $blks*) =>
    tok tk .keyword
    blks.forM (go (a.withBlock .quote))
  | `(block|ul{$items*}) | `(block|ol($_){$items*}) | `(block|dl{$items*}) =>
    items.forM (go a)
  | other =>
    let k := other.getKind
    if k == nullKind || k == ``Lean.Parser.Command.versoCommentBody then
      other.getArgs.forM (go a)

/--
Collects all semantic tokens that can be deduced purely from `Syntax`
without elaboration information.
-/
partial def collectSyntaxBasedSemanticTokens (text : FileMap) : (stx : Syntax) → Array LeanSemanticToken
  | `($e.$id:ident)    =>
    let tokens := collectSyntaxBasedSemanticTokens text e
    tokens.push { stx := id, type := SemanticTokenType.property }
  | `($e |>.$field:ident) =>
    let tokens := collectSyntaxBasedSemanticTokens text e
    tokens.push { stx := field, type := SemanticTokenType.property }
  | stx => Id.run do
    if noHighlightKinds.contains stx.getKind then
      return #[]
    if docKinds.contains stx.getKind then
      -- Verso docstrings have `stx[1]` as a syntax node; plain (CommonMark)
      -- docstrings have `stx[1]` as a single atom whose source span covers
      -- the docstring body.
      if stx[1].isAtom then
        let some ⟨startPos, endPos⟩ := stx[1].getRange?
          | return #[]
        return collectMarkdownTokens text startPos endPos
      else
        return collectVersoTokens text stx[1] (collectSyntaxBasedSemanticTokens text)
    let mut tokens :=
      if stx.isOfKind choiceKind then
        collectSyntaxBasedSemanticTokens text stx[0]
      else
        stx.getArgs.map (collectSyntaxBasedSemanticTokens text) |>.flatten
    let Syntax.atom _ val := stx
      | return tokens
    let isRegularKeyword := val.length > 0 && isIdFirst val.front
    let isHashKeyword := val.length > 1 && val.front == '#' && isIdFirst (String.Pos.Raw.get val ⟨1⟩)
    if ! isRegularKeyword && ! isHashKeyword then
      return tokens
    return tokens.push { stx, type := keywordSemanticTokenMap.getD val .keyword }

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
              return { stx := ti.stx, type := SemanticTokenType.function }
          else if ! localDecl.isImplementationDetail then
            return { stx := ti.stx, type := SemanticTokenType.variable }
    if ti.stx.getKind == Parser.Term.identProjKind then
      return {stx := ti.stx, type := SemanticTokenType.property }
    none

/--
A debugging utility for inspecting sets of collected tokens, classified by line and sorted by
column.
-/
def dbgShowTokens (text : FileMap) (toks : Array LeanSemanticToken) : String := Id.run do
  let mut byLine : Std.HashMap Nat (Array (Nat × Nat × LeanSemanticToken)) := {}
  for ⟨stx, tok, prio⟩ in toks do
    if let some ⟨⟨l, c1⟩, ⟨_, c2⟩⟩ := text.lspRangeOfStx? stx then
      byLine := byLine.alter l fun x? => some (x?.getD #[] |>.push (c1, c2, ⟨stx, tok, prio⟩))
  let mut out := ""
  for (l, vals) in byLine.toList.mergeSort (fun x y => x.1 ≤ y.1) do
    let vals := vals.toList.mergeSort fun x y => x.1 ≤ y.1
    out := out ++ s!"{l}:\t{vals.map (fun (c1, c2, ⟨stx, tok, prio⟩) => (c1, c2, stx, toJson tok, prio))}\n"
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
def handleSemanticTokensFull (_ : SemanticTokensParams) (_ : SemanticTokensState)
    : RequestM (LspResponse SemanticTokens × SemanticTokensState) := do
  let ctx ← read
  let doc ← readDoc
  -- Only grabs the finished prefix so that we do not need to wait for elaboration to complete
  -- for the full file before sending a response. This means that the response will be incomplete,
  -- which we mitigate by regularly sending `workspace/semanticTokens/refresh` requests in the
  -- `FileWorker` to tell the client to re-compute the semantic tokens.
  let (snaps, _, isComplete) ← doc.cmdSnaps.getFinishedPrefixWithTimeout 3000 (cancelTks := ctx.cancelTk.cancellationTasks)
  let response ← computeSemanticTokens doc 0 none snaps
  return ({ response, isComplete }, ⟨⟩)

def handleSemanticTokensDidChange (_ : DidChangeTextDocumentParams)
    : StateT SemanticTokensState RequestM Unit := do
  return

/-- Computes the semantic tokens in the range provided by `p`. -/
def handleSemanticTokensRange (p : SemanticTokensRangeParams)
    : RequestM (RequestTask SemanticTokens) := do
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
