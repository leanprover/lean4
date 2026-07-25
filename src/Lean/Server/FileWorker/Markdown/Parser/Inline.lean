/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Thrane Christiansen
-/
module

prelude
public import Init.Data.String.PosRaw
public import Init.Data.String.TakeDrop
public import Init.Data.Array.Basic
public import Init.While
public import Std.Data.HashMap
public import Lean.Syntax
public import Lean.Server.FileWorker.Markdown.Basic
public import Lean.Server.FileWorker.Markdown.Parser.Block
import Lean.Server.FileWorker.Markdown.Parser.Emphasis

namespace Lean.Server.FileWorker.Markdown

/-!
# Pass 2: Inline Parser

Walks an inline-bearing source range and recovers all Markdown inline elements except embedded HTML.

A backslash escape (`\X`) is treated as two characters of plain text and disables any markup
interpretation of `X`.
-/

/-- Counts consecutive characters equal to `c` at the start of `sub`. -/
def countRun (sub : InlineRange) (c : Char) : Nat × String.Pos.Raw := Id.run do
  let mut sub := sub
  let mut n := 0
  while !sub.isEmpty && sub.front == c do
    n := n + 1
    sub := sub.drop1
  return (n, sub.startPos)

/-- Appends a `text` inline covering `[textStart:pos)` to `out`, if non-empty. -/
def pushText (out : Array Inline) (textStart pos : String.Pos.Raw) : Array Inline :=
  if textStart < pos then
    out.push (.text { start := textStart, stop := pos })
  else out

/--
Whether `c` is in CommonMark's ASCII-punctuation set: ``!"#$%&'()*+,-./:;<=>?@[\]^_\`{|}~``. These
are the only characters that a backslash escape consumes; a backslash before any other character is
a literal backslash followed by the character.
-/
def isAsciiPunctuation (c : Char) : Bool :=
  let n := c.toNat
  (33 ≤ n && n ≤ 47) ||  -- ! " # $ % & ' ( ) * + , - . /
  (58 ≤ n && n ≤ 64) ||  -- : ; < = > ? @
  (91 ≤ n && n ≤ 96) ||  -- [ \ ] ^ _ `
  (123 ≤ n && n ≤ 126)   -- { | } ~

/-- Tries to parse a code span. Caller ensures ``sub.front == '`'``. -/
def code (sub : InlineRange) : Option (Inline × String.Pos.Raw) := do
  let s := sub.source
  let stopPos := sub.stopPos
  let cursor := sub.startPos
  let (openLen, p) := countRun sub '`'
  guard (openLen > 0)
  let openTicks : Syntax.Range := { start := cursor, stop := p }
  let mut rest : InlineRange := s.range p stopPos
  while !rest.isEmpty do
    if rest.front == '`' then
      let q := rest.startPos
      let (runLen, qAfterRun) := countRun rest '`'
      if runLen == openLen then
        let content : Syntax.Range := { start := p, stop := q }
        let closeTicks : Syntax.Range := { start := q, stop := qAfterRun }
        return (.code openTicks content closeTicks, qAfterRun)
      rest := s.range qAfterRun stopPos
    else
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
Tries to parse a URI autolink starting at `start`, which should be the position immediately after
the opening `<`. Returns the position of the closing `>` on success.
-/
def autolinkUri (sub : InlineRange) : Option String.Pos.Raw := do
  let mut rest := sub
  guard <| !rest.isEmpty && rest.front.isAlpha
  rest := rest.drop1
  let mut schemeLen := 1
  while !rest.isEmpty && schemeLen < 32 do
    let c := rest.front
    if c.isAlpha || c.isDigit || c == '+' || c == '-' || c == '.' then
      schemeLen := schemeLen + 1
      rest := rest.drop1
    else break
  guard <| schemeLen ≥ 2
  guard <| !rest.isEmpty && rest.front == ':'
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
Tries to parse an email autolink starting at `start`, which is the position immediately after the
opening `<`. Matches CommonMark §6.5's HTML5-style email regex. Returns the position of the closing
`>` on success.
-/
def autolinkEmail (sub : InlineRange) : Option String.Pos.Raw := do
  let s := sub.source
  let mut rest := sub
  let mut localLen := 0
  while !rest.isEmpty do
    let c := rest.front
    if isEmailLocalChar c then
      localLen := localLen + 1
      rest := rest.drop1
    else break
  guard <| localLen != 0
  guard <| !rest.isEmpty && rest.front == '@'
  rest := rest.drop1
  -- Domain: at least one label.
  while !rest.isEmpty do
    let firstC := rest.front
    guard firstC.isAlphanum
    let labelStart := rest.startPos
    rest := rest.drop1
    let mut labelLen := 1
    while !rest.isEmpty && labelLen < 63 do
      let c := rest.front
      if c.isAlpha || c.isDigit || c == '-' then
        labelLen := labelLen + 1
        rest := rest.drop1
      else break
    -- A label cannot end with a hyphen.
    let labelEndPrev : String.Pos.Raw := { byteIdx := rest.startPos.byteIdx - 1 }
    guard <| (labelEndPrev < labelStart) || labelEndPrev.get s.str != '-'
    guard !rest.isEmpty
    let c := rest.front
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
def autolink (sub : InlineRange) : Option (Inline × String.Pos.Raw) := do
  let s := sub.source
  let stop := sub.stopPos
  let cursor := sub.startPos
  guard <| !sub.isEmpty && sub.front == '<'
  let afterOpen := sub.drop1
  let inner := afterOpen.startPos
  let openAngle : Syntax.Range := { start := cursor, stop := inner }
  let (isLink, closePos) ← ((true, ·) <$> autolinkUri afterOpen) <|> ((false, ·) <$> autolinkEmail afterOpen)
  let closeRest : InlineRange := s.range closePos stop
  if closeRest.isEmpty then failure
  let afterClose := (closeRest.drop1).startPos
  let urlRange : Syntax.Range := { start := inner, stop := closePos }
  let closeAngle : Syntax.Range := { start := closePos, stop := afterClose }
  if isLink then
    return (.autolink openAngle urlRange closeAngle false, afterClose)
  else
    return (.autolink openAngle urlRange closeAngle true, afterClose)

/--
Scans `[…]` (or `![…]`'s alt) for the matching `]`, respecting Markdown's complex error-recovery
rules. Returns the position of the matching `]` if found.
-/
def findCloseBracket (sub : InlineRange) : Option String.Pos.Raw := do
  let s := sub.source
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
      -- advance past it; otherwise the entire opening run is literal
      -- (CommonMark §6.1 — see the matching scanner branch).
      match code rest with
      | some (_, after) => rest := s.range after stop
      | none =>
        let (_, runEnd) := countRun rest '`'
        rest := s.range runEnd stop
    else if c == '<' then
      -- Autolinks (and raw HTML, which we don't support) bind tighter
      -- than link brackets per CommonMark §6.3: a `]` inside an
      -- autolink is part of its URL, not a link close.
      match autolink rest with
      | some (_, after) => rest := s.range after stop
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

/-- Scans for `)` at or after `sub.startPos`, respecting backslash escapes. -/
def findCloseParen (sub : InlineRange) : Option String.Pos.Raw := do
  let mut rest := sub
  while !rest.isEmpty do
    let c := rest.front
    let p := rest.startPos
    let restNext := rest.drop1
    if c == '\\' && !restNext.isEmpty then
      rest := restNext.drop1
    else if c == ')' then
      return p
    else
      rest := restNext
  failure

/-- Skips ASCII whitespace (' ', '\t', '\r', and '\n') at the start of `sub`. -/
def skipInlineWs (sub : InlineRange) : String.Pos.Raw := Id.run do
  let mut sub := sub
  while !sub.isEmpty do
    let c := sub.front
    if c == ' ' || c == '\t' || c == '\n' || c == '\r' then
      sub := sub.drop1
    else break
  return sub.startPos

/--
Parses the body of an inline link/image target, which is the contents between the opening `(` and
its matching `)`. `sub` should begin just after the opening `(`.

 The returned `url` range covers only the URL content (interior of the angle brackets, when
bracketed). Returns `(url, title?, closeParenPos)` on success.
-/
def inlineLinkTarget (sub : InlineRange) :
    Option (Syntax.Range × Option Syntax.Range × String.Pos.Raw) := do
  let s := sub.source
  let stop := sub.stopPos
  let p0 := skipInlineWs sub
  let rest : InlineRange := s.range p0 stop
  let (url, afterUrlByte) ←
    if rest.isEmpty then
      pure ({ start := p0, stop := p0 }, p0)
    else if rest.front == '<' then
      bracketedUrl rest
    else
      unbracketedUrl rest
  let afterUrl := skipInlineWs (s.range afterUrlByte stop)
  let afterUrlRest : InlineRange := s.range afterUrl stop
  if afterUrlRest.isEmpty then failure
  let cAfter := afterUrlRest.front
  let mut title? : Option Syntax.Range := none
  let mut afterTitle := afterUrl
  if cAfter == '"' || cAfter == '\'' || cAfter == '(' then
    let closer : Char := if cAfter == '(' then ')' else cAfter
    let titleStart := (afterUrlRest.drop1).startPos
    let mut titleRest : InlineRange := s.range titleStart stop
    let mut titleEnd? : Option String.Pos.Raw := none
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
    match titleEnd? with
    | none => failure
    | some te =>
      let teRest : InlineRange := s.range te stop
      if teRest.isEmpty then failure
      let afterTe := (teRest.drop1).startPos
      title? := some { start := titleStart, stop := te }
      afterTitle := skipInlineWs (s.range afterTe stop)
  let afterTitleRest : InlineRange := s.range afterTitle stop
  if afterTitleRest.isEmpty then failure
  if afterTitleRest.front != ')' then failure
  return (url, title?, afterTitle)
where
  /--
  Bracketed form `<url>`. The URL content excludes the angle brackets themselves; backslash escapes
  are allowed; an unescaped `<` or `\n` inside fails the whole target. Returns the URL range and the
  position one past the closing `>`.
  -/
  -- Note: deliberately not shared with `autolinkUri` despite the surface similarity. CommonMark
  -- §6.3 (link destinations) recognizes backslash escapes inside `<…>` and accepts whitespace; §6.5
  -- (autolinks) does neither and additionally rejects ASCII control chars. A shared loop would need
  -- to be parameterised on escape mode and character class, which obscures both call sites more
  -- than it deduplicates them.
  bracketedUrl (rest : InlineRange) : Option (Syntax.Range × String.Pos.Raw) := do
    let mut rest := rest.drop1  -- consume opening `<`
    let urlContentStart := rest.startPos
    let mut urlContentEnd := urlContentStart
    let mut afterUrlByte := urlContentStart
    let mut foundClose := false
    while !rest.isEmpty do
      let c := rest.front
      let p := rest.startPos
      let restNext := rest.drop1
      if c == '\\' && !restNext.isEmpty then
        rest := restNext.drop1
      else if c == '>' then
        urlContentEnd := p
        afterUrlByte := restNext.startPos
        foundClose := true
        break
      else if c == '<' || c == '\n' then
        failure
      else
        rest := restNext
    guard foundClose
    return ({ start := urlContentStart, stop := urlContentEnd }, afterUrlByte)
  /--
  Unbracketed form. Stops at whitespace, an ASCII control char, or an unbalanced `)`; balances
  `(`/`)` runs and rejects targets with unmatched opens (CommonMark §6.3: a link destination's
  parens must balance). Returns the URL range and the (same) position right after it.
  -/
  unbracketedUrl (rest : InlineRange) : Option (Syntax.Range × String.Pos.Raw) := do
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
    return ({ start := urlContentStart, stop := urlContentEnd }, urlContentEnd)

/--
Classifies a `*`/`_` delimiter run by the characters that surrounding it, determining whether it can
open or close emphasis. `prevChar`/`nextChar` are the chars immediately before/after the run, with
ASCII space substituted at range boundaries.

Returns a tuple in which the first projection is true when the delimiter run can open emphasis and
the second is true when it can close emphasis.
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
the outer `[…]` (with `openBracket`/`closeBracket` covering the brackets, and `afterClose` one past
the `]`) and parsed its interior as `interior`. This function picks among the inline `(url)`, full
reference `[label]`, collapsed `[]`, and shortcut forms, building the result with `mk` (which closes
over the leading `!` for images).
-/
def linkSuffix
    (refs : RefTable) (s : InlineSource) (stop : String.Pos.Raw)
    (openBracket closeBracket : Syntax.Range) (afterClose : String.Pos.Raw)
    (interior : Array Inline)
    (mk : Syntax.Range → Array Inline → Syntax.Range → LinkTarget → Inline) :
    Option (Inline × String.Pos.Raw) :=
  let afterCloseRest : InlineRange := s.range afterClose stop
  -- Inline form `(url)` takes precedence; on failure, fall back to shortcut
  -- (the second `[` of a reference form would not match here, so the only
  -- other option is shortcut). A second `[` commits to the reference form
  -- — a missing close bracket or unresolved label is a hard failure.
  if !afterCloseRest.isEmpty && afterCloseRest.front == '(' then
    inlineForm afterCloseRest <|> shortcutForm
  else if !afterCloseRest.isEmpty && afterCloseRest.front == '[' then
    referenceForm afterCloseRest
  else
    shortcutForm
where
  /-- The `[…](url)` / `![…](url "title")` form. -/
  inlineForm (afterCloseRest : InlineRange) : Option (Inline × String.Pos.Raw) := do
    let urlStart := (afterCloseRest.drop1).startPos
    let openParen : Syntax.Range := { start := afterClose, stop := urlStart }
    let (url, title?, parenEnd) ←
      inlineLinkTarget (s.range urlStart stop)
    let parenEndRest : InlineRange := s.range parenEnd stop
    guard !parenEndRest.isEmpty
    let afterParen := (parenEndRest.drop1).startPos
    let closeParen : Syntax.Range := { start := parenEnd, stop := afterParen }
    let target := LinkTarget.inline openParen url closeParen title?
    return (mk openBracket interior closeBracket target, afterParen)
  /-- The full `[…][label]` / `![…][label]` and collapsed `[…][]` / `![…][]` forms. -/
  referenceForm (afterCloseRest : InlineRange) : Option (Inline × String.Pos.Raw) := do
    let labelStart := (afterCloseRest.drop1).startPos
    let labelOpen : Syntax.Range := { start := afterClose, stop := labelStart }
    let refEnd ← findCloseBracket (s.range labelStart stop)
    let refEndRest : InlineRange := s.range refEnd stop
    guard !refEndRest.isEmpty
    let afterRefEnd := (refEndRest.drop1).startPos
    let labelClose : Syntax.Range := { start := refEnd, stop := afterRefEnd }
    let isCollapsed := labelStart == refEnd
    -- Collapsed reference: the link text/image alt serves as the label.
    let labelStr :=
      if isCollapsed then InlineSource.extract s openBracket.stop closeBracket.start
      else InlineSource.extract s labelStart refEnd
    let { url, title? } ← refs[normalizeLabel labelStr]?
    let form : ReferenceLinkForm :=
      if isCollapsed then .collapsed labelOpen labelClose
      else .full labelOpen { start := labelStart, stop := refEnd } labelClose
    return (mk openBracket interior closeBracket (.reference url title? form), afterRefEnd)
  /-- The shortcut `[…]` / `![…]` form: the bracket interior itself is the label. -/
  shortcutForm : Option (Inline × String.Pos.Raw) := do
    let labelStr := InlineSource.extract s openBracket.stop closeBracket.start
    let { url, title? } ← refs[normalizeLabel labelStr]?
    return (mk openBracket interior closeBracket (.reference url title? .shortcut), afterClose)

/-!
### Inline Tokenization

The §6.2 emphasis algorithm consumes a flat sequence of tokens, each either a fully-finalized
non-emphasis `Inline` (code span, link, image, autolink, soft/hard break, escaped char) or a
still-raw `*`/`_` delimiter run.  `tokenizeInlines` produces this sequence. It walks the inline
source, recognizes each non-emphasis inline kind in turn (backslash escape §2.4, code span §6.1,
link §6.3, image §6.4, autolink §6.5, hard line break §6.7), and saves delimiter runs for §6.2 to
handle later.

The walker's mutable state (`InlineTokenizerState` below) is touched through three operations:
`recognize` for “matched an inline,” `skipChar` for “no match, this character is literal text,” and
`skipPast` for the one place where we leap forward past several literal chars at once.
-/

/--
The state maintained while walking an inline source and emitting tokens
for §6.2: the tokens emitted so far, the unconsumed input, the start of
any pending plain-text run not yet flushed, and the previous source
character (needed for §6.2's flanking-rule classification of `*`/`_`
runs as openers/closers).

A pending plain-text run is the consecutive characters seen since the
last token boundary that did *not* start any recognized inline; these
are buffered and flushed as a single `.text` inline immediately before
the next emitted token (or at end of input).
-/
structure InlineTokenizerState where
  /-- Tokens emitted so far. -/
  out : Array InlineTok
  /-- The unconsumed input. -/
  rest : InlineRange
  /-- Start of the pending plain-text run not yet flushed. -/
  textStart : String.Pos.Raw
  /--
  The source character immediately before `rest.startPos`. Used to classify emphasis delimiter runs
  as left or right flanking.
  -/
  prevChar : Char

/-- The empty initial state covering `s[start:stop)`. -/
def InlineTokenizerState.init (s : InlineSource) (start stop : String.Pos.Raw) :
    InlineTokenizerState where
  out := #[]
  rest := s.range start stop
  textStart := start
  prevChar := ' '

/-- The state monad for inline tokenization. -/
abbrev TokenizeM := StateM InlineTokenizerState

/--
Handles a recognized inline:
 1. Flushes any pending plain-text run from `textStart` up to `matchStart`.
  2. Appends `tok`.
  3. Advances the walker to `resumeAt`, recording `newPrev` as the post-match flanking character.

Most callers pass `matchStart := cursor` (the position the match began), so all consumed bytes are
emitted exactly once. The line-ending branch passes a *trimmed* position to drop trailing spaces.
-/
def recognize (tok : InlineTok) (matchStart resumeAt : String.Pos.Raw)
    (resumeRest : InlineRange) (newPrev : Char) : TokenizeM Unit :=
  modify fun st =>
    { st with
      out := (pushTokText st.out st.textStart matchStart).push tok,
      rest := resumeRest,
      textStart := resumeAt,
      prevChar := newPrev
    }

/--
The current character did not start a recognized inline. Advances one character, accumulating it
into the pending plain-text run.
-/
def skipChar : TokenizeM Unit := modify fun st =>
  { st with rest := st.rest.drop1, prevChar := st.rest.front }

/--
Advances multiple characters as plain text.

This is used when a code span is not properly closed, forcing its opener to become text instead.
-/
def skipPast (newRest : InlineRange) (newPrev : Char) : TokenizeM Unit :=
  modify fun st => { st with rest := newRest, prevChar := newPrev }

/-- Flushes residual pending text and returns the final token array. -/
def finalizeTokens : TokenizeM (Array InlineTok) := do
  let st ← get
  return pushTokText st.out st.textStart st.rest.startPos

mutual

/--
Parses the inline content of a substring into a flat array of inlines.
-/
partial def parseInlinesInRange (refs : RefTable) (s : InlineSource) (start stop : String.Pos.Raw) :
    Array Inline :=
  processEmphasis (tokenizeInlines refs s start stop)

/--
Tokenizes the inline content of a block into a flat sequence of already-finalized non-emphasis
inlines and unprocessed emphasis delimiter runs. Emphasis matching is deferred to `processEmphasis`.
-/
partial def tokenizeInlines (refs : RefTable) (s : InlineSource) (start stop : String.Pos.Raw) :
    Array InlineTok :=
  let go : TokenizeM (Array InlineTok) := do
    while !(← get).rest.isEmpty do
      let st ← get
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
          recognize (.inline (.hardBreak { start := cursor, stop := cursorNext }))
            cursor escapedNext restAfterEsc ' '
        else if isAsciiPunctuation nextC then
          recognize (.inline (.text { start := cursorNext, stop := escapedNext }))
            cursor escapedNext restAfterEsc nextC
        else
          skipChar
      else if c == '`' then
        match code st.rest with
        | some (codeSpan, after) =>
          recognize (.inline codeSpan) cursor after (s.range after stop) '`'
        | none =>
          let (_, runEnd) := countRun st.rest '`'
          skipPast (s.range runEnd stop) '`'
      else if c == '!' && !restNext.isEmpty && restNext.front == '[' then
        match image refs s cursor stop with
        | some (img, after) =>
          recognize (.inline img) cursor after (s.range after stop) ')'
        | none => skipChar
      else if c == '[' then
        match link refs s cursor stop with
        | some (link, after) =>
          recognize (.inline link) cursor after (s.range after stop) ')'
        | none => skipChar
      else if c == '<' then
        match autolink st.rest with
        | some (autolink, after) =>
          recognize (.inline autolink) cursor after (s.range after stop) '>'
        | none => skipChar
      else if c == '\n' then
        -- A line ending normalizes to a soft break (or, with two or more trailing spaces, a hard
        -- break — §6.7). Per §4.8 paragraph-content normalization, trailing whitespace before the
        -- line ending is dropped in either case so it doesn't leak into the rendered output.
        let mut q := cursor
        while q > st.textStart && (String.Pos.Raw.prev s.str q).get s.str == ' ' do
          q := String.Pos.Raw.prev s.str q
        let spaces := cursor.byteIdx - q.byteIdx
        -- The emitted token's stop must be one byte past the `\n` itself; `cursorNext` skips across
        -- the inter-line gap to the next line's first non-whitespace position (correct for the
        -- walker but would make the token range cover the gap).
        let stopPastNewline : String.Pos.Raw := ⟨cursor.byteIdx + 1⟩
        if spaces >= 2 then
          recognize (.inline (.hardBreak { start := q, stop := stopPastNewline }))
            q cursorNext restNext ' '
        else
          -- Soft break: emit the bare `\n` as a standalone text inline so the trimmed text and any
          -- following text stay separate (and the renderer's soft break rendering remains a single
          -- `\n`).
          recognize (.inline (.text { start := cursor, stop := stopPastNewline }))
            q cursorNext restNext '\n'
      else if c == '*' || c == '_' then
        let (n, runEnd) := countRun st.rest c
        let runEndRest : InlineRange := s.range runEnd stop
        let nextC := if !runEndRest.isEmpty then runEndRest.front else ' '
        let (canOpen, canClose) := classifyDelim c st.prevChar nextC
        recognize
          (.delim { startPos := cursor, endPos := runEnd, ch := c, origLen := n, canOpen, canClose })
          cursor runEnd runEndRest c
      else
        skipChar
    finalizeTokens
  go.run' (.init s start stop)

/--
Whether `inlines` contains a link or autolink element, recursively descending into emphasis but
*not* into images. Per CommonMark §6.3, a link's text may not contain another link at any level of
nesting. If it does, the outer link is suppressed and its bracket characters become literal text.
Images are excluded because the spec explicitly permits images inside link text, and links inside
those images' alt text.
-/
partial def containsLink (inlines : Array Inline) : Bool :=
  inlines.any fun i => match i with
    | .link ..     => true
    | .autolink .. => true
    | .italic _ content _ => containsLink content
    | .bold _ content _ => containsLink content
    | _ => false

/--
Locates the outer `[…]` of a link or image at `cursor`, parses its interior, and hands off to
`parseLinkSuffix` to decide which `[…]…` form applies. `prefixLen` is the number of characters
preceding the opening `[` consumed at `cursor` (0 for links, 1 for `!` of images).

Returns `none` when no `[…]` is present, when the closing bracket is missing, or when `reject?`
rejects the parsed interior. `reject?` implements CommonMark §6.3's “links may not contain other
links” rule for links. Images pass `none`.
-/
partial def bracketed
    (refs : RefTable) (s : InlineSource) (cursor stop : String.Pos.Raw)
    (prefixLen : Nat)
    (reject? : Option (Array Inline → Bool))
    (mk : Syntax.Range → Array Inline → Syntax.Range → LinkTarget → Inline) :
    Option (Inline × String.Pos.Raw) := do
  let cursorRest : InlineRange := s.range cursor stop
  -- Step over the (possibly empty) prefix to reach the `[`.
  let mut p := cursorRest
  for _ in [0 : prefixLen] do
    guard !p.isEmpty
    p := p.drop1
  guard <| !p.isEmpty && p.front == '['
  let bracketStart := p.startPos
  let interiorStart := (p.drop1).startPos
  let openBracket : Syntax.Range := { start := bracketStart, stop := interiorStart }
  let bracketEnd ← findCloseBracket (s.range interiorStart stop)

  let bracketEndRest : InlineRange := s.range bracketEnd stop
  guard !bracketEndRest.isEmpty
  let afterClose := (bracketEndRest.drop1).startPos
  let closeBracket : Syntax.Range := { start := bracketEnd, stop := afterClose }
  let interior := parseInlinesInRange refs s interiorStart bracketEnd
  if let some r := reject? then
    guard !(r interior)
  linkSuffix refs s stop openBracket closeBracket afterClose interior mk

/-- Tries to parse a link `[text](url)`, `[text][ref]`, `[text][]`, or `[text]`. -/
partial def link (refs : RefTable) (s : InlineSource) (cursor stop : String.Pos.Raw) :
    Option (Inline × String.Pos.Raw) :=
  -- CommonMark §6.3: a link's text may not contain another link at any
  -- level of nesting. If it does, the outer link is not formed: its
  -- bracket characters fall through to literal text and the inner link
  -- survives.
  bracketed refs s cursor stop 0 (some containsLink) .link

/--
Tries to parse `![alt](url)`, `![alt][ref]`, `![alt][]`, or `![alt]`.
-/
partial def image (refs : RefTable) (s : InlineSource) (cursor stop : String.Pos.Raw) :
    Option (Inline × String.Pos.Raw) := do
  -- Bang range covers just the `!`; `tryParseBracketed` skips it via
  -- `prefixLen := 1` and finds the `[` that follows.
  let cursorRest : InlineRange := s.range cursor stop
  guard !cursorRest.isEmpty
  let bang : Syntax.Range := { start := cursor, stop := (cursorRest.drop1).startPos }
  bracketed refs s cursor stop 1 none (.image bang)

end

/--
Parses the inline content of a single source range into a flat array of inlines. The range is
typically a paragraph's full extent or a heading's content slice.
-/
public def parseInlines (refs : RefTable) (s : InlineSource) (range : Syntax.Range) : Array Inline :=
  parseInlinesInRange refs s range.start range.stop
