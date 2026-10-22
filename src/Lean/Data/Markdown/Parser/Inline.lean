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
import Lean.Data.Markdown.Parser.Emphasis

namespace Lean.Markdown


/-!
# Pass 2: Inline Parser

Parses the inline elements of a block's text, except embedded HTML.

A backslash escape `\X` of an ASCII punctuation character becomes an `Inline.escape`.
-/

variable {s : String.Slice}

/-- Counts consecutive characters equal to `c` at the start of `sub`, returning the count and the
position after them. -/
def countSequence (sub : InlineCursor s) (c : Char) : Nat × s.Pos := Id.run do
  let mut sub := sub
  let mut n := 0
  while sub.front? == some c do
    n := n + 1
    sub := sub.drop1
  return (n, sub.startPos)

/-- Tries to parse a code span. Caller ensures ``sub.front == '`'``. -/
def code (sub : InlineCursor s) : Option (Inline s × s.Pos) := do
  let src := sub.source
  let stopPos := sub.stopPos
  let cursor := sub.startPos
  let (openLen, p) := countSequence sub '`'
  guard (openLen > 0)
  let openTicks := subsliceClamped cursor p
  let mut rest : InlineCursor s := src.cursor p stopPos
  while !rest.isEmpty do
    if rest.front? == some '`' then
      let q := rest.startPos
      let (seqLen, qAfterSequence) := countSequence rest '`'
      if seqLen == openLen then
        let content := src.linesBetween p q
        let closeTicks := subsliceClamped q qAfterSequence
        return (.code openTicks content closeTicks, qAfterSequence)
      rest := src.cursor qAfterSequence stopPos
    else
      rest := rest.drop1
  failure

/--
Tries to parse a character reference at the beginning of `sub`, which must point at `&`. Returns the
resulting `Inline.entity` and the position past the closing `;` on success.
-/
def characterReference (sub : InlineCursor s) : Option (Inline s × s.Pos) := do
  let start := sub.startPos
  let mut rest := sub.drop1
  let mut body := ""
  while !rest.isEmpty do
    let c := rest.front
    if c == ';' then
      let value ← characterReference? body
      let after := rest.drop1.startPos
      return (.entity (subsliceClamped start after) value, after)
    guard (isCharacterReferenceChar c)
    body := body.push c
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
Tries to parse a URI autolink at `sub`, which should begin immediately after the opening `<`.
Returns the position of the closing `>` on success.
-/
def autolinkUri (sub : InlineCursor s) : Option s.Pos := do
  let mut rest := sub
  guard <| rest.front?.any Char.isAlpha
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
    guard !(c == '<' || c == ' ' || c == '\t' || c == '\n' || c == '\r')
    -- Reject ASCII control characters (0x7f is DEL, the others are below 0x20)
    guard <| c.toNat ≥ 0x20 && c.toNat != 0x7f
    rest := rest.drop1
  failure

/--
Tries to parse an email autolink at `sub`, which should begin immediately after the opening `<`.
Matches CommonMark §6.5's HTML5-style email regex. Returns the position of the closing `>` on
success.
-/
def autolinkEmail (sub : InlineCursor s) : Option s.Pos := do
  let mut rest := sub
  let mut localLen := 0
  while rest.front?.any isEmailLocalChar do
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
Tries to parse an autolink at the beginning of `sub` (which must point at `<`). Returns the resulting
`Inline.autolink` and the position past the closing `>` on success.
-/
def autolink (sub : InlineCursor s) : Option (Inline s × s.Pos) := do
  let src := sub.source
  let stop := sub.stopPos
  let openAngle ← sub.charSubslice?
  guard <| sub.front? == some '<'
  let afterOpen := sub.drop1
  let inner := afterOpen.startPos
  let (isLink, closePos) ←
    ((true, ·) <$> autolinkUri afterOpen) <|> ((false, ·) <$> autolinkEmail afterOpen)
  let closeRest : InlineCursor s := src.cursor closePos stop
  let closeAngle ← closeRest.charSubslice?
  let urlRange := subsliceClamped inner closePos
  return (.autolink openAngle urlRange closeAngle !isLink, closeAngle.endExclusive)

/--
Scans `[…]` (or `![…]`'s alt) for the matching `]`, respecting Markdown's complex error-recovery
rules. Returns the position of the matching `]` if found.
-/
def findCloseBracket (sub : InlineCursor s) : Option s.Pos := do
  let src := sub.source
  let stop := sub.stopPos
  let mut rest := sub
  let mut depth : Nat := 0
  while !rest.isEmpty do
    let c := rest.front
    let p := rest.startPos
    let restNext := rest.drop1
    if c == '\\' && !restNext.isEmpty then
      rest := restNext.drop1
    else if c == '`' then
      -- Code spans bind tighter than link brackets. If a span forms,
      -- advance past it; otherwise the entire opening sequence is literal
      -- (CommonMark §6.1; see the matching scanner branch).
      match code rest with
      | some (_, after) => rest := src.cursor after stop
      | none =>
        let (_, seqEnd) := countSequence rest '`'
        rest := src.cursor seqEnd stop
    else if c == '<' then
      -- Autolinks (and raw HTML, which we don't support) bind tighter
      -- than link brackets per CommonMark §6.3: a `]` inside an
      -- autolink is part of its URL, not a link close.
      match autolink rest with
      | some (_, after) => rest := src.cursor after stop
      | none => rest := restNext
    else if c == '[' then
      depth := depth + 1
      rest := restNext
    else if c == ']' then
      if depth == 0 then return p
      else depth := depth - 1
      rest := restNext
    else
      rest := restNext
  failure

/-- Skips ASCII whitespace (' ', '\t', '\r', and '\n') at the start of `sub`. -/
def skipInlineWs (sub : InlineCursor s) : s.Pos := Id.run do
  let mut sub := sub
  while sub.front?.any fun c => c == ' ' || c == '\t' || c == '\n' || c == '\r' do
    sub := sub.drop1
  return sub.startPos

/--
Parses the body of an inline link/image target, which is the contents between the opening `(` and
its matching `)`. `sub` should begin just after the opening `(`.

Returns `(destination, title?, closeParenPos)` on success.
-/
def inlineLinkTarget (sub : InlineCursor s) :
    Option (LinkDestination s × Option (LinkTitle s) × s.Pos) := do
  let src := sub.source
  let stop := sub.stopPos
  let p0 := skipInlineWs sub
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
  if cAfter == '"' || cAfter == '\'' || cAfter == '(' then
    let closer : Char := if cAfter == '(' then ')' else cAfter
    let opener ← afterUrlRest.charSubslice?
    let titleStart := opener.endExclusive
    let mut titleRest : InlineCursor s := src.cursor titleStart stop
    let mut titleEnd? : Option s.Pos := none
    while !titleRest.isEmpty do
      let c := titleRest.front
      let q := titleRest.startPos
      let titleRestNext := titleRest.drop1
      if c == '\\' && !titleRestNext.isEmpty then
        titleRest := titleRestNext.drop1
      else if c == closer then
        titleEnd? := some q
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
  Bracketed form `<url>`. Backslash escapes are allowed; an unescaped `<` or `\n` inside fails the
  whole target. Returns the destination and the position one past the closing `>`.
  -/
  bracketedUrl (rest : InlineCursor s) : Option (LinkDestination s × s.Pos) := do
    let openAngle ← rest.charSubslice?
    let mut rest := rest.drop1
    let urlContentStart := rest.startPos
    while !rest.isEmpty do
      let c := rest.front
      let p := rest.startPos
      let restNext := rest.drop1
      if c == '\\' && !restNext.isEmpty then
        rest := restNext.drop1
      else if c == '>' then
        let closeAngle ← rest.charSubslice?
        let destination : LinkDestination s :=
          { angles? := some (openAngle, closeAngle), url := subsliceClamped urlContentStart p }
        return (destination, closeAngle.endExclusive)
      else if c == '<' || c == '\n' then
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
      if c == '\\' && !restNext.isEmpty then
        rest := restNext.drop1
      else if c == ' ' || c == '\t' || c == '\n' || c == '\r' then
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
    return ({ angles? := none, url := subsliceClamped urlContentStart urlContentEnd }, urlContentEnd)

/--
Classifies a `*`/`_` delimiter sequence by the characters that surround it, determining whether it
can open or close emphasis. `prevChar`/`nextChar` are the chars immediately before/after the
sequence, with ASCII space substituted at the boundaries of the input.

Returns a tuple in which the first projection is true when the delimiter sequence can open emphasis
and the second is true when it can close emphasis.
-/
def classifyDelim (ch prevChar nextChar : Char) : Bool × Bool :=
  let beforeWs := prevChar.isWhitespace
  let afterWs := nextChar.isWhitespace
  let beforePunct := isAsciiPunctuation prevChar
  let afterPunct := isAsciiPunctuation nextChar
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
Parses the common suffix logic for `[…]…` links and `![…]…` images: the caller has already located
the outer `[…]` (with `openBracket`/`closeBracket` the brackets, and `afterClose` one
past the `]`) and parsed its interior as `interior`. This function picks among the inline `(url)`,
full reference `[label]`, collapsed `[]`, and shortcut forms, building the result with `mk` (which
closes over the leading `!` for images).
-/
def linkSuffix
    (refs : RefTable s) (src : InlineSource s) (stop : s.Pos)
    (openBracket closeBracket : s.Subslice) (afterClose : s.Pos)
    (interior : Array (Inline s))
    (mk : s.Subslice → Array (Inline s) → s.Subslice → LinkTarget s → Inline s) :
    Option (Inline s × s.Pos) :=
  let afterCloseRest : InlineCursor s := src.cursor afterClose stop
  -- Inline form `(url)` takes precedence; on failure, fall back to shortcut
  -- (the second `[` of a reference form would not match here, so the only
  -- other option is shortcut). A second `[` commits to the reference form,
  -- so a missing close bracket or unresolved label is a hard failure.
  if afterCloseRest.front? == some '(' then
    inlineForm afterCloseRest <|> shortcutForm
  else if afterCloseRest.front? == some '[' then
    referenceForm afterCloseRest
  else
    shortcutForm
where
  /-- The `[…](url)` / `![…](url "title")` form. -/
  inlineForm (afterCloseRest : InlineCursor s) : Option (Inline s × s.Pos) := do
    let openParen ← afterCloseRest.charSubslice?
    let (destination, title?, parenEnd) ← inlineLinkTarget (src.cursor openParen.endExclusive stop)
    let closeParen ← (src.cursor parenEnd stop).charSubslice?
    let target := LinkTarget.inline openParen destination closeParen title?
    return (mk openBracket interior closeBracket target, closeParen.endExclusive)
  /-- The full `[…][label]` / `![…][label]` and collapsed `[…][]` / `![…][]` forms. -/
  referenceForm (afterCloseRest : InlineCursor s) : Option (Inline s × s.Pos) := do
    let labelOpen ← afterCloseRest.charSubslice?
    let labelStart := labelOpen.endExclusive
    let refEnd ← findCloseBracket (src.cursor labelStart stop)
    let labelClose ← (src.cursor refEnd stop).charSubslice?
    let isCollapsed := labelStart == refEnd
    -- Collapsed reference: the link text/image alt serves as the label.
    let (labelStr, label) :=
      if isCollapsed then
        (src.extract openBracket.endExclusive closeBracket.startInclusive,
         src.linesBetween openBracket.endExclusive closeBracket.startInclusive)
      else (src.extract labelStart refEnd, src.linesBetween labelStart refEnd)
    let definition ← refs[normalizeLabel labelStr]?
    let form : ReferenceLinkForm s :=
      if isCollapsed then .collapsed labelOpen labelClose else .full labelOpen labelClose
    return (mk openBracket interior closeBracket (.reference definition label form),
      labelClose.endExclusive)
  /-- The shortcut `[…]` / `![…]` form: the bracket interior itself is the label. -/
  shortcutForm : Option (Inline s × s.Pos) := do
    let labelStr := src.extract openBracket.endExclusive closeBracket.startInclusive
    let definition ← refs[normalizeLabel labelStr]?
    let label := src.linesBetween openBracket.endExclusive closeBracket.startInclusive
    return (mk openBracket interior closeBracket (.reference definition label .shortcut), afterClose)

/-!
### Inline Tokenization

The §6.2 emphasis algorithm consumes a flat sequence of tokens, each either a fully-finalized
non-emphasis `Inline` (code span, link, image, autolink, soft/hard break, escaped char) or a
still-raw `*`/`_` delimiter sequence.  `tokenizeInlines` produces this sequence. It reads the inline
source, recognizes each non-emphasis inline kind in turn (backslash escape §2.4, character reference
§2.5, code span §6.1, link §6.3, image §6.4, autolink §6.5, hard line break §6.7, soft line break
§6.8), and saves delimiter sequences for §6.2 to handle later.

The tokenizer's mutable state (`InlineTokenizerState` below) is touched through three operations:
`recognize` for “matched an inline,” `skipChar` for “no match, this character is literal text,” and
`skipPast` for the one place where we leap forward past several literal chars at once.
-/

/--
The state maintained while tokenizing an inline source and emitting tokens
for §6.2: the tokens emitted so far, the unconsumed input, the start of
any pending plain text not yet flushed, and the previous source
character (needed for §6.2's flanking-rule classification of `*`/`_`
sequences as openers/closers).

The pending plain text is the consecutive characters seen since the
last token boundary that did *not* start any recognized inline; these
are buffered and flushed as a single `.text` inline immediately before
the next emitted token (or at end of input).
-/
structure InlineTokenizerState (s : String.Slice) where
  /-- Tokens emitted so far. -/
  out : Array (InlineTok s)
  /-- The unconsumed input. -/
  rest : InlineCursor s
  /-- Start of the pending plain text not yet flushed. -/
  textStart : s.Pos
  /--
  The source character immediately before `rest.startPos`. Used to classify emphasis delimiter
  sequences as left or right flanking.
  -/
  prevChar : Char

/-- The initial state for the part of `src` from `start` to `stop`. -/
def InlineTokenizerState.init (src : InlineSource s) (start stop : s.Pos) :
    InlineTokenizerState s where
  out := #[]
  rest := src.cursor start stop
  textStart := start
  prevChar := ' '

/-- The state monad for inline tokenization. -/
abbrev TokenizeM (s : String.Slice) := StateM (InlineTokenizerState s)

/--
Handles a recognized inline:
1. Flushes any pending plain text from `textStart` up to `matchStart`.
2. Appends `tok`.
3. Advances the tokenizer to `resumeAt`, recording `newPrev` as the post-match flanking character.

Most callers pass `matchStart := cursor` (the position the match began), so all consumed characters
are emitted exactly once. The line-ending branch passes a *trimmed* position to drop trailing spaces.
-/
def recognize (tok : InlineTok s) (matchStart resumeAt : s.Pos)
    (resumeRest : InlineCursor s) (newPrev : Char) : TokenizeM s Unit :=
  modify fun st =>
    { st with
      out := (pushTokText st.out st.textStart matchStart).push tok,
      rest := resumeRest,
      textStart := resumeAt,
      prevChar := newPrev
    }

/--
The current character did not start a recognized inline. Advances one character, accumulating it
into the pending plain text.
-/
def skipChar : TokenizeM s Unit := modify fun st =>
  { st with rest := st.rest.drop1, prevChar := st.rest.front }

/--
Advances multiple characters as plain text.

This is used when a code span is not properly closed, forcing its opener to become text instead.
-/
def skipPast (newRest : InlineCursor s) (newPrev : Char) : TokenizeM s Unit :=
  modify fun st => { st with rest := newRest, prevChar := newPrev }

/-- Flushes residual pending text and returns the final token array. -/
def finalizeTokens : TokenizeM s (Array (InlineTok s)) := do
  let st ← get
  return pushTokText st.out st.textStart st.rest.startPos

mutual

/--
Parses the inline content of a substring into a flat array of inlines.
-/
partial def parseInlinesInRange (refs : RefTable s) (src : InlineSource s) (start stop : s.Pos) :
    Array (Inline s) :=
  processEmphasis (tokenizeInlines refs src start stop)

/--
Tokenizes the inline content of a block into a flat sequence of already-finalized non-emphasis
inlines and unprocessed emphasis delimiter sequences. Emphasis matching is deferred to
`processEmphasis`.
-/
partial def tokenizeInlines (refs : RefTable s) (src : InlineSource s) (start stop : s.Pos) :
    Array (InlineTok s) :=
  let go : TokenizeM s (Array (InlineTok s)) := do
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
        if nextC == '\n' then
          -- Backslash before a line ending is a hard line break (§6.7).
          match restNext.charSubslice? with
          | some newline =>
            recognize (.inline (.hardBreak charSubslice newline)) cursor escapedNext restAfterEsc ' '
          | none => skipChar
        else if isAsciiPunctuation nextC then
          let escapedRange := (restNext.charSubslice?).getD (subsliceClamped cursorNext escapedNext)
          recognize (.inline (.escape charSubslice escapedRange)) cursor escapedNext restAfterEsc nextC
        else
          skipChar
      else if c == '`' then
        match code st.rest with
        | some (codeSpan, after) =>
          recognize (.inline codeSpan) cursor after (src.cursor after stop) '`'
        | none =>
          let (_, seqEnd) := countSequence st.rest '`'
          skipPast (src.cursor seqEnd stop) '`'
      else if c == '!' && restNext.front? == some '[' then
        match image refs src cursor stop with
        | some (img, after) =>
          recognize (.inline img) cursor after (src.cursor after stop) ')'
        | none => skipChar
      else if c == '[' then
        match link refs src cursor stop with
        | some (link, after) =>
          recognize (.inline link) cursor after (src.cursor after stop) ')'
        | none => skipChar
      else if c == '<' then
        match autolink st.rest with
        | some (autolink, after) =>
          recognize (.inline autolink) cursor after (src.cursor after stop) '>'
        | none => skipChar
      else if c == '&' then
        match characterReference st.rest with
        | some (entity, after) =>
          recognize (.inline entity) cursor after (src.cursor after stop) ';'
        | none => skipChar
      else if c == '\n' then
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
        -- `cursorNext` skips across the inter-line gap to the next line's first non-whitespace
        -- position, which is right for the tokenizer; the break itself ends after the `\n`.
        if spaces >= 2 then
          recognize (.inline (.hardBreak (subsliceClamped q cursor) charSubslice)) q cursorNext restNext ' '
        else
          recognize (.inline (.softBreak charSubslice)) q cursorNext restNext '\n'
      else if c == '*' || c == '_' then
        let (n, seqEnd) := countSequence st.rest c
        let seqEndRest : InlineCursor s := src.cursor seqEnd stop
        let nextC := seqEndRest.front?.getD ' '
        let (canOpen, canClose) := classifyDelim c st.prevChar nextC
        recognize
          (.delim { startPos := cursor, endPos := seqEnd, ch := c, origLen := n, canOpen, canClose })
          cursor seqEnd seqEndRest c
      else
        skipChar
    finalizeTokens
  go.run' (.init src start stop)

/--
Whether `inlines` contains a link or autolink element, recursively descending into emphasis but
*not* into images. Per CommonMark §6.3, a link's text may not contain another link at any level of
nesting. If it does, the outer link is suppressed and its bracket characters become literal text.
Images are excluded because the spec explicitly permits images inside link text, and links inside
those images' alt text.
-/
partial def containsLink (inlines : Array (Inline s)) : Bool :=
  inlines.any fun i => match i with
    | .link ..     => true
    | .autolink .. => true
    | .italic _ content _ => containsLink content
    | .bold _ content _ => containsLink content
    | _ => false

/--
Locates the outer `[…]` of a link or image at `cursor`, parses its interior, and hands off to
`linkSuffix` to decide which `[…]…` form applies. `prefixLen` is the number of characters preceding
the opening `[` consumed at `cursor` (0 for links, 1 for `!` of images).

Returns `none` when no `[…]` is present, when the closing bracket is missing, when no link form
follows the brackets, or when `reject?` rejects the parsed interior. `reject?` implements CommonMark §6.3's “links may not contain other
links” rule for links. Images pass `none`.
-/
partial def bracketed
    (refs : RefTable s) (src : InlineSource s) (cursor stop : s.Pos)
    (prefixLen : Nat)
    (reject? : Option (Array (Inline s) → Bool))
    (mk : s.Subslice → Array (Inline s) → s.Subslice → LinkTarget s → Inline s) :
    Option (Inline s × s.Pos) := do
  let cursorRest : InlineCursor s := src.cursor cursor stop
  -- Step over the (possibly empty) prefix to reach the `[`.
  let mut p := cursorRest
  for _ in [0 : prefixLen] do
    guard !p.isEmpty
    p := p.drop1
  guard <| p.front? == some '['
  let openBracket ← p.charSubslice?
  let interiorStart := openBracket.endExclusive
  let bracketEnd ← findCloseBracket (src.cursor interiorStart stop)
  let closeBracket ← (src.cursor bracketEnd stop).charSubslice?
  let interior := parseInlinesInRange refs src interiorStart bracketEnd
  if let some r := reject? then
    guard !(r interior)
  linkSuffix refs src stop openBracket closeBracket closeBracket.endExclusive interior mk

/-- Tries to parse a link `[text](url)`, `[text][ref]`, `[text][]`, or `[text]`. -/
partial def link (refs : RefTable s) (src : InlineSource s) (cursor stop : s.Pos) :
    Option (Inline s × s.Pos) :=
  -- CommonMark §6.3: a link's text may not contain another link at any
  -- level of nesting. If it does, the outer link is not formed: its
  -- bracket characters fall through to literal text and the inner link
  -- survives.
  bracketed refs src cursor stop 0 (some containsLink) .link

/--
Tries to parse `![alt](url)`, `![alt][ref]`, `![alt][]`, or `![alt]`.
-/
partial def image (refs : RefTable s) (src : InlineSource s) (cursor stop : s.Pos) :
    Option (Inline s × s.Pos) := do
  -- The bang is the `!` alone; `bracketed` skips it via `prefixLen := 1` and finds the `[`
  -- that follows.
  let bang ← (src.cursor cursor stop).charSubslice?
  bracketed refs src cursor stop 1 none (.image bang)

end

/--
Parses the inline content of `src`, typically a paragraph or a heading's content, into a flat array
of inlines.
-/
public def parseInlines (refs : RefTable s) (src : InlineSource s) : Array (Inline s) :=
  parseInlinesInRange refs src src.startPos src.stopPos
