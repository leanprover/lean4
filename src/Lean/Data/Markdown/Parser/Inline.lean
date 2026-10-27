/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Thrane Christiansen
-/
module

prelude
public import Init.Data.Array.Basic
public import Init.While
public import Std.Data.HashMap
public import Lean.Data.Markdown.Basic
public import Lean.Data.Markdown.Text
public import Lean.Data.Markdown.InlineSource
public import Lean.Data.Markdown.Parser.Block
import Lean.Data.Markdown.Unicode.CharacterClasses
import Lean.Data.Markdown.Parser.Emphasis
import Lean.Data.Markdown.Parser.Html

namespace Lean.Markdown


/-!
# Pass 2: Inline Parser

Parses the inline elements of a block's text.

A backslash escape `\X` of an ASCII punctuation character becomes an `Inline.escape`.
-/

variable {s : String.Slice}

/-- Counts consecutive characters equal to `c` at the start of `cur`, returning the count and the
position after them. -/
def countSequence (cur : InlineCursor s) (c : Char) : Nat × s.Pos :=
  let (after, n) := cur.takeSequence c
  (n, after.startPos)

/--
Parses a character reference at `cur`, which must point at `&`. Returns the resulting
`Inline.entity` and the position past the closing `;`.
-/
def parseCharacterReference? (cur : InlineCursor s) : Option (Inline s × s.Pos) := do
  let start := cur.startPos
  let bodyStart := cur.drop1.startPos
  let mut rest := cur.drop1
  while !rest.isEmpty do
    let c := rest.front
    if c == ';' then
      let value ← characterReference? (subsliceClamped bodyStart rest.startPos)
      let after := rest.drop1.startPos
      return (.entity (subsliceClamped start after) value, after)
    guard (isCharacterReferenceChar c)
    rest := rest.drop1
  failure

/--
Whether `c` is in the email autolink local-part character set (CommonMark §6.5): ASCII alphanumerics
plus ``.!#$%&'*+/=?^_`{|}~-``.
-/
def isEmailLocalChar (c : Char) : Bool :=
  c.isAlpha || c.isDigit || c == '.' || c == '!' || c == '#'
  || c == '$' || c == '%' || c == '&' || c == '\'' || c == '*'
  || c == '+' || c == '/' || c == '=' || c == '?' || c == '^'
  || c == '_' || c == '`' || c == '{' || c == '|' || c == '}'
  || c == '~' || c == '-'

/--
Parses a URI autolink at `cur`, which should begin immediately after the opening `<`. Returns the
position of the closing `>`.
-/
def parseAutolinkUri? (cur : InlineCursor s) : Option s.Pos := do
  let mut rest := cur
  guard <| Option.any Char.isAlpha rest.front?
  rest := rest.drop1
  let mut schemeLen := 1
  while !rest.isEmpty && schemeLen < 32 do
    let c := rest.front
    if c.isAlpha || c.isDigit || c == '+' || c == '-' || c == '.' then
      schemeLen := schemeLen + 1
      rest := rest.drop1
    else break
  guard <| schemeLen ≥ 2
  guard <| rest.front? == some ':'
  rest := rest.drop1
  while !rest.isEmpty do
    let c := rest.front
    if c == '>' then return rest.startPos
    guard !(c == '<' || c.isWhitespace)
    -- Reject ASCII control characters (0x7f is DEL, the others are below 0x20)
    guard <| c.toNat ≥ 0x20 && c.toNat != 0x7f
    rest := rest.drop1
  failure

/--
Parses an email autolink at `cur`, which should begin immediately after the opening `<`, following
CommonMark §6.5's HTML5-style email regex. Returns the position of the closing `>`.
-/
def parseAutolinkEmail? (cur : InlineCursor s) : Option s.Pos := do
  let mut rest := cur
  let mut localLen := 0
  while Option.any isEmailLocalChar rest.front? do
    localLen := localLen + 1
    rest := rest.drop1
  guard <| localLen != 0
  guard <| rest.front? == some '@'
  rest := rest.drop1
  -- Domain: at least one label.
  while !rest.isEmpty do
    let firstC := rest.front
    guard firstC.isAlphanum
    rest := rest.drop1
    let mut labelLen := 1
    let mut lastC := firstC
    while labelLen < 63 do
      let some c := rest.front? | break
      if c.isAlpha || c.isDigit || c == '-' then
        labelLen := labelLen + 1
        lastC := c
        rest := rest.drop1
      else break
    -- A label cannot end with a hyphen.
    guard <| lastC != '-'
    let some c := rest.front? | failure
    if c == '>' then
      return rest.startPos
    if c == '.' then
      rest := rest.drop1
    else
      failure
  failure

/--
Parses an autolink at `cur`, which must point at `<`. Returns the resulting `Inline.autolink` and
the position past the closing `>`.
-/
def parseAutolink? (cur : InlineCursor s) : Option (Inline s × s.Pos) := do
  let src := cur.source
  let stop := cur.stopPos
  let openAngle ← cur.charSubslice?
  guard <| cur.front? == some '<'
  let afterOpen := cur.drop1
  let inner := afterOpen.startPos
  let (isLink, closePos) ←
    ((true, ·) <$> parseAutolinkUri? afterOpen) <|> ((false, ·) <$> parseAutolinkEmail? afterOpen)
  let closeRest : InlineCursor s := src.cursor closePos stop
  let closeAngle ← closeRest.charSubslice?
  let urlRange := subsliceClamped inner closePos
  return (.autolink openAngle urlRange closeAngle !isLink, closeAngle.endExclusive)

/--
Parses raw HTML (CommonMark §6.6) at `cur`, which must point at `<`: an open tag, a closing tag, a
comment, a processing instruction, a declaration, or a CDATA section. Returns the `Inline.html` and
the position after its closing `>`.
-/
def parseRawHtml? (cur : InlineCursor s) : Option (Inline s × s.Pos) := do
  guard <| cur.front? == some '<'
  let afterOpen := cur.drop1
  let after ←
    match afterOpen.front? with
    | some '/' => parseClosingTag? afterOpen.drop1
    | some '?' => parseProcessingInstruction? afterOpen.drop1
    | some '!' => parseMarkupDeclaration? afterOpen.drop1
    | some c => if c.isAlpha then parseOpenTag? afterOpen else none
    | none => none
  return (.html (cur.source.linesBetween cur.startPos after.startPos), after.startPos)

/-- Skips the spaces, tabs, and line endings at the start of `cur`. -/
def skipInlineWs (cur : InlineCursor s) : s.Pos := Id.run do
  let mut cur := cur
  while Option.any Char.isWhitespace cur.front? do
    cur := cur.drop1
  return cur.startPos

/--
Parses the body of an inline link/image target, which is the contents between the opening `(` and
its matching `)`. `cur` should begin just after the opening `(`.

Returns `(destination, title?, closeParenPos)` on success.
-/
def parseInlineLinkTarget? (cur : InlineCursor s) :
    Option (LinkDestination s × Option (LinkTitle s) × s.Pos) := do
  let src := cur.source
  let stop := cur.stopPos
  let p0 := skipInlineWs cur
  let rest : InlineCursor s := src.cursor p0 stop
  let (destination, afterUrl) ←
    if rest.isEmpty then
      pure ({ angles? := none, url := subsliceClamped p0 p0 }, p0)
    else if rest.front == '<' then
      bracketedUrl rest
    else
      unbracketedUrl rest
  let afterUrlWs := skipInlineWs (src.cursor afterUrl stop)
  let afterUrlRest : InlineCursor s := src.cursor afterUrlWs stop
  let cAfter ← afterUrlRest.front?
  let mut title? : Option (LinkTitle s) := none
  let mut afterTitle := afterUrlWs
  -- A title must be separated from the destination by whitespace (CommonMark §6.3).
  if (cAfter == '"' || cAfter == '\'' || cAfter == '(') && afterUrlWs != afterUrl then
    let closer : Char := if cAfter == '(' then ')' else cAfter
    let opener ← afterUrlRest.charSubslice?
    let titleStart := opener.endExclusive
    let mut titleRest : InlineCursor s := src.cursor titleStart stop
    let mut titleEnd? : Option s.Pos := none
    while !titleRest.isEmpty do
      let c := titleRest.front
      let q := titleRest.startPos
      let titleRestNext := titleRest.drop1
      if c == '\\' && Option.any isAsciiPunctuation titleRestNext.front? then
        titleRest := titleRestNext.drop1
      else if c == closer then
        titleEnd? := some q
        break
      else if c == '(' && closer == ')' then
        -- An unescaped `(` inside a parenthesized title fails the title (CommonMark §6.3).
        break
      else
        titleRest := titleRestNext
    let te ← titleEnd?
    let closerRange ← (src.cursor te stop).charSubslice?
    title? := some { opener, content := src.linesBetween titleStart te, closer := closerRange }
    afterTitle := skipInlineWs (src.cursor closerRange.endExclusive stop)
  let afterTitleRest : InlineCursor s := src.cursor afterTitle stop
  guard <| afterTitleRest.front? == some ')'
  return (destination, title?, afterTitle)
where
  /--
  Bracketed form `<url>`. Backslash escapes are allowed; an unescaped `<` or line ending inside
  fails the whole target. Returns the destination and the position one past the closing `>`.
  -/
  bracketedUrl (rest : InlineCursor s) : Option (LinkDestination s × s.Pos) := do
    let openAngle ← rest.charSubslice?
    let mut rest := rest.drop1
    let urlContentStart := rest.startPos
    while !rest.isEmpty do
      let c := rest.front
      let p := rest.startPos
      let restNext := rest.drop1
      if c == '\\' && Option.any isAsciiPunctuation restNext.front? then
        rest := restNext.drop1
      else if c == '>' then
        let closeAngle ← rest.charSubslice?
        let destination : LinkDestination s :=
          { angles? := some (openAngle, closeAngle), url := subsliceClamped urlContentStart p }
        return (destination, closeAngle.endExclusive)
      else if c == '<' || c == '\n' || c == '\r' then
        failure
      else
        rest := restNext
    failure
  /--
  Unbracketed form. Stops at whitespace, an ASCII control char, or an unbalanced `)`; balances
  `(`/`)` pairs and rejects targets with unmatched opens (CommonMark §6.3: a link destination's
  parens must balance). Returns the destination and the (same) position right after it.
  -/
  unbracketedUrl (rest : InlineCursor s) : Option (LinkDestination s × s.Pos) := do
    let urlContentStart := rest.startPos
    let mut rest := rest
    let mut parenDepth : Nat := 0
    while !rest.isEmpty do
      let c := rest.front
      let restNext := rest.drop1
      if c == '\\' && Option.any isAsciiPunctuation restNext.front? then
        rest := restNext.drop1
      else if c.isWhitespace then
        break
      else if c == '(' then
        parenDepth := parenDepth + 1
        rest := restNext
      else if c == ')' then
        if parenDepth == 0 then break
        parenDepth := parenDepth - 1
        rest := restNext
      else if c.toNat < 0x20 then
        break
      else
        rest := restNext
    guard (parenDepth == 0)
    let urlContentEnd := rest.startPos
    return ({ angles? := none, url := subsliceClamped urlContentStart urlContentEnd },
      urlContentEnd)

/--
Classifies a `*`/`_` delimiter sequence by the characters that surround it, determining whether it
can open or close emphasis. `prevChar`/`nextChar` are the chars immediately before/after the
sequence, with ASCII space substituted at the boundaries of the input.

Returns a tuple in which the first projection is true when the delimiter sequence can open emphasis
and the second is true when it can close emphasis.
-/
def classifyDelim (ch prevChar nextChar : Char) : Bool × Bool :=
  let beforeWs := isUnicodeWhitespace prevChar
  let afterWs := isUnicodeWhitespace nextChar
  let beforePunct := isUnicodePunctuation prevChar
  let afterPunct := isUnicodePunctuation nextChar
  let leftFlanking := !afterWs && (!afterPunct || beforeWs || beforePunct)
  let rightFlanking := !beforeWs && (!beforePunct || afterWs || afterPunct)
  let canOpen :=
    if ch == '*' then leftFlanking
    else leftFlanking && (!rightFlanking || beforePunct)
  let canClose :=
    if ch == '*' then rightFlanking
    else rightFlanking && (!leftFlanking || afterPunct)
  (canOpen, canClose)

/--
Whether the input after `cur` is a link label (CommonMark §6.3): at most 999 characters and no
unescaped brackets.
-/
def isLinkLabel (cur : InlineCursor s) : Bool := Id.run do
  let mut cur := cur
  let mut len := 0
  while !cur.isEmpty do
    if len ≥ 999 then return false
    let c := cur.front
    cur := cur.drop1
    len := len + 1
    if c == '\\' && Option.any isAsciiPunctuation cur.front? then
      cur := cur.drop1
      len := len + 1
    else if c == '[' || c == ']' then
      return false
  return true

/-- The monad for parsing link targets. Failure is `none`. -/
abbrev LinkTargetM (s : String.Slice) := ReaderT (InlineContext s) Option

/-- The reference target that `label` refers to. Fails when there is none. -/
@[inline] def linkRef (label : Lines s) : LinkTargetM s (RefTarget s) := do
  let some target := (← refTable)[normalizeLabel label]? | failure
  return target

/--
Parses the target of a `[…]…` link or `![…]…` image, after the caller has located the outer `[…]`
(with `openBracket`/`closeBracket` the brackets, and `afterClose` one past the `]`). This function
picks among the inline `(url)`, full reference `[label]`, collapsed `[]`, and shortcut forms, and
returns the target together with the position after it.
-/
def parseLinkSuffix? (openBracket closeBracket : s.Subslice) (afterClose : s.Pos) :
    LinkTargetM s (LinkTarget s × s.Pos) := do
  let src ← inlineSource
  let afterCloseRest : InlineCursor s := src.cursor afterClose src.stopPos
  -- Inline form `(url)` takes precedence; on failure, fall back to shortcut. A link label or `[]`
  -- commits to the reference form, so an unresolved label is a hard failure; any other `[` leaves
  -- the shortcut form.
  if afterCloseRest.front? == some '(' then
    inlineForm afterCloseRest <|> shortcutForm
  else if afterCloseRest.front? == some '[' then
    referenceForm afterCloseRest
  else
    shortcutForm
where
  /-- The `[…](url)` / `![…](url "title")` form. -/
  inlineForm (afterCloseRest : InlineCursor s) : LinkTargetM s (LinkTarget s × s.Pos) := do
    let src ← inlineSource
    let openParen ← afterCloseRest.charSubslice?
    let (destination, title?, parenEnd) ←
      parseInlineLinkTarget? (src.cursor openParen.endExclusive src.stopPos)
    let closeParen ← (src.cursor parenEnd src.stopPos).charSubslice?
    return (.inline openParen destination closeParen title?, closeParen.endExclusive)
  /--
  The full `[…][label]` / `![…][label]` and collapsed `[…][]` / `![…][]` forms. `afterCloseRest` is
  at the `[` after the link text. When a link label or `[]` follows, the link is a reference link in
  that form, and it fails when the label doesn't match any definition. When the `[` doesn't begin a
  link label, the link text is tried as a shortcut reference instead.
  -/
  referenceForm (afterCloseRest : InlineCursor s) : LinkTargetM s (LinkTarget s × s.Pos) := do
    -- Without definitions, there's no sense attempting to parse the label because it can never
    -- resolve.
    guard !(← refTable).isEmpty
    let labelOpen ← afterCloseRest.charSubslice?
    let afterOpen := afterCloseRest.drop1
    if afterOpen.front? == some ']' then
      -- Collapsed reference: the link text/image alt serves as the label.
      let labelClose ← afterOpen.charSubslice?
      let label ← interiorLabel?
      let target ← linkRef label
      return (.reference target label (.collapsed labelOpen labelClose),
        labelClose.endExclusive)
    else
      match parseLinkLabel? afterOpen with
      | none => shortcutForm
      | some (label, atClose) =>
        let labelClose ← atClose.charSubslice?
        let target ← linkRef label
        return (.reference target label (.full labelOpen labelClose), labelClose.endExclusive)
  /-- The shortcut `[…]` / `![…]` form: the bracket interior itself is the label. -/
  shortcutForm : LinkTargetM s (LinkTarget s × s.Pos) := do
    guard !(← refTable).isEmpty
    let label ← interiorLabel?
    let target ← linkRef label
    return (.reference target label .shortcut, afterClose)
  /-- The lines of the bracket interior, if it is a link label. -/
  interiorLabel? : LinkTargetM s (Lines s) := do
    let src ← inlineSource
    guard (isLinkLabel (src.cursor openBracket.endExclusive closeBracket.startInclusive))
    return src.linesBetween openBracket.endExclusive closeBracket.startInclusive

/-!
### Inline Tokenization

The §6.2 emphasis algorithm consumes a flat sequence of tokens, each either a fully-finalized
non-emphasis `Inline` (inline code, link, image, autolink, soft/hard break, escaped char) or a
still-raw `*`/`_` delimiter sequence.  `tokenizeInlines` produces this sequence. It reads the inline
source, recognizes each non-emphasis inline kind in turn (backslash escape §2.4, character reference
§2.5, inline code §6.1, link §6.3, image §6.4, autolink §6.5, raw HTML §6.6, hard line break §6.7,
soft line break §6.8), and saves delimiter sequences for §6.2 to handle later.

Links and images follow the bracket-stack procedure of the specification's appendix. A `[` or `![`
is emitted as a text token and pushed on a stack of bracket openers. A `]` pops the nearest opener
and tries to parse a link target or reference after itself. On success, the tokens that were emitted
since the opener become the link's text, with their emphasis processed, and the opener's text token
is replaced by the link or image; every earlier `[` is then deactivated, since a link may not
contain a link. On failure, the brackets stay text. Each `]` thus does work proportional to the
tokens since its opener.

The tokenizer's mutable state (`InlineTokenizerState` below) is touched through a few operations:
`recognize` for “matched an inline,” `skipChar` for “no match, this character is literal text,”
`skipPast` for the one place where we leap forward past several literal chars at once, and
`openBracket`/`closeBracket` for the bracket stack.
-/

/-- A `[` or `![` that may begin a link or image. -/
structure BracketOpener (s : String.Slice) where
  /--
  The index in the output of the opener's text token. The tokens after it are the link's text.
  -/
  tokIdx : Nat
  /-- The `!` of an image opener. -/
  bang? : Option s.Subslice
  /-- The `[`. -/
  openBracket : s.Subslice
  /-- Whether the opener may still form a link. A `[` before a completed link may not. -/
  active : Bool := true
deriving Inhabited

/--
The state of the inline tokenizer, which turns an inline source into the sequence of tokens that
emphasis matching (CommonMark §6.2) consumes.

Consecutive characters that don't begin any inline construct are pending plain text. They become a
single `.text` inline immediately before the next token, or at the end of the input. The character
before the unconsumed input is kept because the flanking rules (CommonMark §6.2) classify a `*` or
`_` sequence by the characters on both sides of it.
-/
structure InlineTokenizerState (s : String.Slice) where
  /-- Tokens that have been emitted so far. -/
  out : Array (InlineTok s)
  /-- The unconsumed input. -/
  rest : InlineCursor s
  /-- Start of the pending plain text that has not yet been flushed. -/
  textStart : s.Pos
  /--
  The source character immediately before `rest.startPos`. Used to classify emphasis delimiter
  sequences as left or right flanking.
  -/
  prevChar : Char
  /-- The bracket openers that have not yet been closed, innermost last. -/
  brackets : Array (BracketOpener s) := #[]
  /--
  The start of the last backtick sequence of each length that a search for closing backticks has
  passed. Once a search has reached the end of the input, a later search for a length whose last
  sequence starts at or before its opener fails without reading the input.
  -/
  lastBacktickSequence : Std.HashMap Nat s.Pos := {}
  /-- Whether a search for closing backticks has reached the end of the input. -/
  backticksScanned : Bool := false

/-- The initial state for `src`. -/
def InlineTokenizerState.init (src : InlineSource s) : InlineTokenizerState s where
  out := #[]
  rest := src.cursor src.startPos src.stopPos
  textStart := src.startPos
  prevChar := ' '

/--
The monad for inline tokenization.
-/
abbrev TokenizeM (s : String.Slice) :=
  ReaderT (InlineContext s) (StateM (InlineTokenizerState s))

/--
Emits the token `tok` for an inline construct that begins at `matchStart`, and resumes tokenizing
with the input `resumeRest`. `newPrev` is the character before that input, which is used for the
flanking rules.

The pending plain text ends where the construct begins, so it becomes a `.text` inline before
`tok`. For a line break, the construct begins before the trailing spaces of the line: two or more
of them are the hard line break itself (CommonMark §6.7), and fewer are removed with the soft line
break (CommonMark §6.8).
-/
def recognize (tok : InlineTok s) (matchStart : s.Pos) (resumeRest : InlineCursor s)
    (newPrev : Char) : TokenizeM s Unit :=
  modify fun st =>
    { st with
      out := (pushTokText st.out st.textStart matchStart).push tok,
      rest := resumeRest,
      textStart := resumeRest.startPos,
      prevChar := newPrev
    }

/--
The current character did not start a recognized inline. Advances one character, accumulating it
into the pending plain text.
-/
def skipChar : TokenizeM s Unit := modify fun st =>
  { st with rest := st.rest.drop1, prevChar := st.rest.front }

/--
Whether `c` may begin an inline construct or a line ending: a backslash escape, inline code, an
image or link bracket, an autolink or raw HTML, a character reference, an emphasis delimiter, or,
with the `latexMath` extension, LaTeX math.
-/
def mayBeginInline (extensions : Extensions) (c : Char) : Bool :=
  c == '\\' || c == '`' || c == '!' || c == '[' || c == ']' || c == '<' || c == '&' || c == '*' ||
  c == '_' || c == '\n' || c == '\r' || (extensions.latexMath && c == '$')

/--
Advances over plain text: the current character, which did not begin an inline construct, and the
characters after it that can't begin one.

The state is updated once for the whole stretch, and the last character becomes the previous
character for the flanking rules.
-/
def skipText : TokenizeM s Unit := do
  let extensions ← extensions
  modify fun st =>
    let rest := st.rest.drop1.skipWhile (!mayBeginInline extensions ·)
    -- The stretch stays within one line, since a line ending may begin an inline construct, so the
    -- character before the new position is the last one consumed.
    { st with rest, prevChar := (rest.startPos.prev? >>= (·.get?)).getD st.rest.front }

/--
Advances multiple characters as plain text.

This is used when inline code is not properly closed, forcing its opener to become text instead.
-/
def skipPast (newRest : InlineCursor s) (newPrev : Char) : TokenizeM s Unit :=
  modify fun st => { st with rest := newRest, prevChar := newPrev }

/--
Parses inline code at `cur`, which must point at a backtick: an opening backtick sequence, the
content, and a closing sequence of the same length (CommonMark §6.1).

A search for the closing sequence records the start of every backtick sequence that it passes, by
length. Once a search has reached the end of the input, a later search for a length whose last
recorded sequence is at or before the opener fails at once, so over a whole paragraph the searches
cost time linear in its length.
-/
def parseCode? (cur : InlineCursor s) : TokenizeM s (Option (Inline s × s.Pos)) := do
  let src := cur.source
  let stopPos := cur.stopPos
  let start := cur.startPos
  let (openLen, p) := countSequence cur '`'
  if openLen == 0 then return none
  let st ← get
  if st.backticksScanned then
    match st.lastBacktickSequence[openLen]? with
    | some last => if last ≤ start then return none
    | none => return none
  let openTicks := subsliceClamped start p
  let mut rest : InlineCursor s := src.cursor p stopPos
  while !rest.isEmpty do
    if rest.front? == some '`' then
      let q := rest.startPos
      let (seqLen, qAfterSequence) := countSequence rest '`'
      -- A search that began later may have passed a later sequence already, so the entry only moves
      -- forward.
      modify fun st =>
        if Option.any (q ≤ ·) st.lastBacktickSequence[seqLen]? then st
        else { st with lastBacktickSequence := st.lastBacktickSequence.insert seqLen q }
      if seqLen == openLen then
        let content := src.linesBetween p q
        let closeTicks := subsliceClamped q qAfterSequence
        return some (.code openTicks ⟨content⟩ closeTicks, qAfterSequence)
      rest := src.cursor qAfterSequence stopPos
    else
      rest := rest.drop1
  modify fun st => { st with backticksScanned := true }
  return none

/-- Flushes residual pending text and returns the final token array. -/
def finalizeTokens : TokenizeM s (Array (InlineTok s)) := do
  let st ← get
  return pushTokText st.out st.textStart st.rest.startPos

/--
Emits a `[` or `![` (with `bang?` the `!`) as a text token and pushes it on the bracket stack. The
input resumes at `resumeRest`, just after the `[`.
-/
def openBracket (bang? : Option s.Subslice) (bracket : s.Subslice) (resumeRest : InlineCursor s) :
    TokenizeM s Unit :=
  modify fun st =>
    -- The output is taken out of the state so that it stays unique and is extended in place.
    let out := st.out
    let st := { st with out := #[] }
    let start := (bang?.getD bracket).startInclusive
    let out := pushTokText out st.textStart start
    { st with
      out := out.push (.inline (.text (subsliceClamped start bracket.endExclusive)))
      brackets := st.brackets.push { tokIdx := out.size, bang?, openBracket := bracket }
      rest := resumeRest
      textStart := bracket.endExclusive
      prevChar := '[' }

/--
Handles a `]`, following the specification's *look for link or image* procedure. With an active
opener on the bracket stack and a link target or reference after the `]`, the tokens since the
opener become the text of a link or image that replaces them; otherwise the `]` is literal text. The
opener is popped in either case, and a completed link deactivates every earlier `[`.
-/
def closeBracket (closeBracket : s.Subslice) : TokenizeM s Unit := do
  let ctx ← read
  let src ← inlineSource
  let some opener := (← get).brackets.back? | skipChar
  let popOpener : TokenizeM s Unit := modify fun st => { st with brackets := st.brackets.pop }
  if !opener.active then
    popOpener
    skipChar
  else
    let stop := src.stopPos
    let afterClose := closeBracket.endExclusive
    match (parseLinkSuffix? opener.openBracket closeBracket afterClose).run ctx with
    | some (target, after) =>
      -- The output is taken out of the state so that it is shrunk and extended in place.
      let out ← modifyGet fun st => (st.out, { st with out := #[] })
      let out := pushTokText out (← get).textStart closeBracket.startInclusive
      let interior := processEmphasis ctx (out.extract (opener.tokIdx + 1) out.size)
      let inl : Inline s :=
        match opener.bang? with
        | some bang => .image bang opener.openBracket interior closeBracket target
        | none => .link opener.openBracket interior closeBracket target
      modify fun st =>
        { st with
          out := (out.shrink opener.tokIdx).push (.inline inl)
          brackets := deactivateBelow st.brackets.pop opener.bang?.isNone
          rest := src.cursor after stop
          textStart := after
          prevChar := (after.prev? >>= (·.get?)).getD ')' }
    | none =>
      popOpener
      skipChar
where
  /--
  After a link forms, every `[` opener still on the stack is deactivated, since a link may not
  contain a link. Openers below an inactive one are already inactive, so the walk stops there.
  -/
  deactivateBelow (brackets : Array (BracketOpener s)) (isLink : Bool) :
      Array (BracketOpener s) := Id.run do
    unless isLink do return brackets
    let mut brackets := brackets
    let mut i := brackets.size
    while i > 0 do
      i := i - 1
      let b := brackets[i]!
      if b.bang?.isSome then continue
      if !b.active then break
      brackets := brackets.set! i { b with active := false }
    return brackets

/--
Tokenizes the inline content of a block into a flat sequence of already-finalized non-emphasis
inlines and unprocessed emphasis delimiter sequences. Emphasis matching is deferred to
`processEmphasis`.
-/
def tokenizeInlines : TokenizeM s (Array (InlineTok s)) := do
  let src ← inlineSource
  let extensions ← extensions
  let stop := src.stopPos
  repeat
    let st ← get
    -- The subslice of the current character, which exists exactly when input remains.
    let some charSubslice := st.rest.charSubslice? | break
    let c := st.rest.front
    let cursor := st.rest.startPos
    let restNext := st.rest.drop1
    let cursorNext := restNext.startPos
    if c == '\\' && !restNext.isEmpty then
      let nextC := restNext.front
      let restAfterEsc := restNext.drop1
      let escapedNext := restAfterEsc.startPos
      if let some (ending, afterEnding) := restNext.parseLineEnding? then
        -- Backslash before a line ending is a hard line break (§6.7).
        recognize (.inline (.hardBreak charSubslice ending)) cursor afterEnding ' '
      else if isAsciiPunctuation nextC then
        let escapedRange := (restNext.charSubslice?).getD (subsliceClamped cursorNext escapedNext)
        recognize (.inline (.escape charSubslice escapedRange)) cursor restAfterEsc nextC
      else
        skipChar
    else if c == '`' then
      match ← parseCode? st.rest with
      | some (inlineCode, after) =>
        recognize (.inline inlineCode) cursor (src.cursor after stop) '`'
      | none =>
        let (_, seqEnd) := countSequence st.rest '`'
        skipPast (src.cursor seqEnd stop) '`'
    else if c == '!' && restNext.front? == some '[' then
      match restNext.charSubslice? with
      | some bracket => openBracket (some charSubslice) bracket restNext.drop1
      | none => skipChar
    else if c == '[' then
      openBracket none charSubslice restNext
    else if c == ']' then
      closeBracket charSubslice
    else if c == '<' then
      match parseAutolink? st.rest <|> parseRawHtml? st.rest with
      | some (inl, after) =>
        recognize (.inline inl) cursor (src.cursor after stop) '>'
      | none => skipChar
    else if c == '&' then
      match parseCharacterReference? st.rest with
      | some (entity, after) =>
        recognize (.inline entity) cursor (src.cursor after stop) ';'
      | none => skipChar
    else if let some (ending, afterEnding) := st.rest.parseLineEnding? then
      -- A line ending normalizes to a soft break (or, with two or more trailing spaces, a hard
      -- break, §6.7). Per §4.8 paragraph-content normalization, trailing spaces before the line
      -- ending are dropped in either case so they don't leak into the rendered output.
      let mut q := cursor
      let mut spaces := 0
      while st.textStart < q do
        match q.prev? with
        | some p =>
          if p.get? == some ' ' then
            q := p
            spaces := spaces + 1
          else break
        | none => break
      -- `afterEnding` begins at the next line's first non-whitespace character, which is where
      -- the tokenizer resumes; the break itself is the whole line ending.
      if spaces >= 2 then
        recognize (.inline (.hardBreak (subsliceClamped q cursor) ending)) q afterEnding ' '
      else
        recognize (.inline (.softBreak ending)) q afterEnding '\n'
    else if c == '$' && extensions.latexMath then
      -- A sequence of one or two dollar signs is a math delimiter (md4c's rules): it may open
      -- after whitespace or punctuation, which includes the start of a line, and may close before
      -- whitespace or punctuation, which includes the end of the input. Longer sequences are
      -- text.
      let (n, seqEnd) := countSequence st.rest c
      let seqEndRest : InlineCursor s := src.cursor seqEnd stop
      if n ≤ 2 then
        let canOpen := isUnicodeWhitespace st.prevChar || isUnicodePunctuation st.prevChar
        let canClose := match seqEndRest.front? with
          | none => true
          | some d => isUnicodeWhitespace d || isUnicodePunctuation d
        recognize
          (.delim { startPos := cursor, ch := c, origLen := n, canOpen, canClose })
          cursor seqEndRest c
      else
        skipPast seqEndRest c
    else if c == '*' || c == '_' then
      let (n, seqEnd) := countSequence st.rest c
      let seqEndRest : InlineCursor s := src.cursor seqEnd stop
      let nextC := seqEndRest.front?.getD ' '
      let (canOpen, canClose) := classifyDelim c st.prevChar nextC
      recognize
        (.delim { startPos := cursor, ch := c, origLen := n, canOpen, canClose })
        cursor seqEndRest c
    else
      skipText
  finalizeTokens

/--
Parses the inline content of `src`, typically a paragraph or a heading's content, into a flat array
of inlines.
-/
public def parseInlines (refs : RefTable s) (src : InlineSource s)
    (extensions : Extensions := {}) : Array (Inline s) :=
  let ctx : InlineContext s := { refs, src, extensions }
  processEmphasis ctx ((tokenizeInlines.run ctx).run' (.init src))
