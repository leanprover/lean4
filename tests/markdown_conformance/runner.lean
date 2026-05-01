/-
Conformance runner for the CommonMark reference test suite.

Usage:
  lean --run tests/markdown_conformance/runner.lean [path/to/spec.txt]

Defaults to `tests/markdown_conformance/spec.txt`.

Reads the spec source directly: examples are embedded in long-backtick
fences (`````… example`), with `.` separating the markdown input from the
expected HTML output. The literal `→` character in spec.txt represents a
tab and is converted at extraction time. Section names are tracked from
`##` headings.

Each extracted example is fed through `parseDocument` and the
`Markdown.Html` renderer; the output is compared byte-for-byte against the
expected HTML. The runner prints a per-section pass/fail tally and exits 0
on full agreement, 1 otherwise.

Obtain the spec source with:

  curl -L -o tests/markdown_conformance/spec.txt \\
    https://raw.githubusercontent.com/commonmark/commonmark-spec/master/spec.txt
-/
module
import Lean.Server.FileWorker.Markdown
import all Lean.Server.FileWorker.Markdown.Parser.Inline
import Std.Data.HashMap
import Std.Data.TreeMap.Lemmas

open Std
open Lean.Server.FileWorker.Markdown

/-!
## CommonMark HTML rendering (test-only)

A simple HTML renderer for the `Block (Array Inline)` tree produced by
`Lean.Server.FileWorker.Markdown.parseDocument`. This lives inside the
conformance runner because nothing else in the toolchain needs it: the
language server emits semantic tokens, not HTML.

The renderer aims for byte-identical output with the CommonMark reference
implementation on the constructs we support, but does not attempt to
faithfully implement the full spec. It is primarily a conformance-suite
oracle: feed Markdown to `parseDocument` plus this renderer, compare to
the expected HTML, and tally divergences.
-/

namespace Lean.Server.FileWorker.Markdown.Html

private def escapeChar : Char → String
  | '&' => "&amp;"
  | '<' => "&lt;"
  | '>' => "&gt;"
  | '"' => "&quot;"
  | c   => c.toString

/-- HTML-escape `&`, `<`, `>`, and `"`. -/
def escape (s : String) : String :=
  s.foldl (init := "") fun acc c => acc ++ escapeChar c

/-- Substring of `source` covered by `r`. -/
def extract (source : String) (r : Syntax.Range) : String :=
  String.Pos.Raw.extract source r.start r.stop

/--
Strips backslash escapes from a string so that `\X` becomes `X` whenever `X`
is an ASCII punctuation character; backslashes before any other character
are preserved verbatim. This matches CommonMark's normalisation of
non-inline-parsed slots like link URLs and titles, where the inline
delimiter machinery cannot run but escapes still apply.
-/
private def unescape (s : String) : String :=
  let (out, pendingBackslash) := s.foldl (init := ("", false)) fun (out, escaped) c =>
    if escaped then
      if isAsciiPunctuation c then (out.push c, false)
      else (out.push '\\' |>.push c, false)
    else if c == '\\' then (out, true)
    else (out.push c, false)
  if pendingBackslash then out.push '\\' else out

private def hexDigit (n : Nat) : Char :=
  if n < 10 then Char.ofNat (n + '0'.toNat)
  else Char.ofNat (n - 10 + 'A'.toNat)

private def appendHex2 (out : String) (n : Nat) : String :=
  out.push '%' |>.push (hexDigit (n / 16)) |>.push (hexDigit (n % 16))

/--
Whether `c` is an ASCII character that should pass through URL
percent-encoding unchanged. Matches the cmark "safe" set used by
CommonMark conformance tests: alphanumerics plus the URL-syntax
punctuation `-_.~!$&'()*+,;=:@/?#`. The `%` character is treated
specially by the caller to preserve existing percent-encoded sequences;
brackets `[`/`]` and braces are *not* in the set because cmark
percent-encodes them in autolink-style URLs.
-/
private def isUrlSafe (c : Char) : Bool :=
  let n := c.toNat
  ('0'.toNat ≤ n && n ≤ '9'.toNat) ||
  ('A'.toNat ≤ n && n ≤ 'Z'.toNat) ||
  ('a'.toNat ≤ n && n ≤ 'z'.toNat) ||
  c == '-' || c == '_' || c == '.' || c == '~'
  || c == '!' || c == '$' || c == '&' || c == '\''
  || c == '(' || c == ')' || c == '*' || c == '+'
  || c == ',' || c == ';' || c == '='
  || c == ':' || c == '@' || c == '/' || c == '?'
  || c == '#'

private def isHexDigit (c : Char) : Bool :=
  let n := c.toNat
  ('0'.toNat ≤ n && n ≤ '9'.toNat)
  || ('a'.toNat ≤ n && n ≤ 'f'.toNat)
  || ('A'.toNat ≤ n && n ≤ 'F'.toNat)

/--
Appends the UTF-8 encoding of `c` to `out`, with each byte emitted as
`%HH`. Used for non-ASCII URL chars per CommonMark's conformance
expectations.
-/
private def appendUtf8Encoded (out : String) (c : Char) : String := Id.run do
  let n := c.toNat
  let mut out := out
  if n < 0x80 then
    out := appendHex2 out n
  else if n < 0x800 then
    out := appendHex2 out (0xC0 + n / 0x40)
    out := appendHex2 out (0x80 + n % 0x40)
  else if n < 0x10000 then
    out := appendHex2 out (0xE0 + n / 0x1000)
    out := appendHex2 out (0x80 + (n / 0x40) % 0x40)
    out := appendHex2 out (0x80 + n % 0x40)
  else
    out := appendHex2 out (0xF0 + n / 0x40000)
    out := appendHex2 out (0x80 + (n / 0x1000) % 0x40)
    out := appendHex2 out (0x80 + (n / 0x40) % 0x40)
    out := appendHex2 out (0x80 + n % 0x40)
  return out

private def hexDigitVal? (c : Char) : Option Nat :=
  let n := c.toNat
  if '0'.toNat ≤ n && n ≤ '9'.toNat then some (n - '0'.toNat)
  else if 'a'.toNat ≤ n && n ≤ 'f'.toNat then some (n - 'a'.toNat + 10)
  else if 'A'.toNat ≤ n && n ≤ 'F'.toNat then some (n - 'A'.toNat + 10)
  else none

private def decDigitVal? (c : Char) : Option Nat :=
  let n := c.toNat
  if '0'.toNat ≤ n && n ≤ '9'.toNat then some (n - '0'.toNat) else none

/--
Decodes an HTML5 entity body — the text between `&` and `;` — to the
corresponding character. Handles numeric character references
(`#NN` decimal and `#xHH`/`#XHH` hex) and a small list of named ASCII
entities (`amp`, `lt`, `gt`, `quot`, `apos`, `nbsp`). The CommonMark
conformance suite's named-entity expectations are skipped at the
runner level, so this minimal table is enough for our purposes.
Returns `none` if the body doesn't decode to a recognised entity, in
which case the caller leaves the original `&...;` text in place.
-/
private def decodeEntityBody (body : String) : Option String := Id.run do
  let sl := body.toSlice
  if sl.isEmpty then return none
  if sl.startsWith '#' then
    let rest := sl.drop 1
    if rest.isEmpty then return none
    let isHex := rest.startsWith 'x' || rest.startsWith 'X'
    let digits := if isHex then rest.drop 1 else rest
    if digits.isEmpty then return none
    let mut n : Nat := 0
    let mut count : Nat := 0
    for c in digits do
      count := count + 1
      if count > 7 then return none
      match (if isHex then hexDigitVal? c else decDigitVal? c) with
      | none => return none
      | some d => n := n * (if isHex then 16 else 10) + d
    -- HTML5: the replacement char (U+FFFD) is used for the null
    -- character, code points outside Unicode, and surrogates.
    if n == 0 || n > 0x10ffff then return some (Char.ofNat 0xfffd).toString
    if n ≥ 0xd800 && n ≤ 0xdfff then return some (Char.ofNat 0xfffd).toString
    return some (Char.ofNat n).toString
  match body with
  | "amp"  => return some "&"
  | "lt"   => return some "<"
  | "gt"   => return some ">"
  | "quot" => return some "\""
  | "apos" => return some "'"
  | "nbsp" => return some (Char.ofNat 0xa0).toString
  | _      => return none

/--
Decodes HTML entity references in `s` — both numeric (`&#10;`/`&#x0A;`)
and the small named-entity table above. Unrecognised `&…;` sequences
pass through unchanged so the surrounding `escape` step renders them
verbatim.
-/
def decodeEntities (s : String) : String := Id.run do
  let mut sl := s.toSlice
  let mut out := ""
  while !sl.isEmpty do
    if sl.startsWith '&' then
      -- Search for `;` within reasonable distance, bailing on whitespace
      -- or another `&`/`<` so we don't scan unbounded stretches of text.
      let mut scan := sl.drop 1
      let mut body := ""
      let mut count : Nat := 0
      let mut foundSemi := false
      while !scan.isEmpty && count < 32 do
        if scan.startsWith ';' then
          foundSemi := true; break
        if scan.startsWith fun c =>
            c == ' ' || c == '\t' || c == '\n' || c == '\r' || c == '<' || c == '&' then
          break
        body := body.push scan.front
        scan := scan.drop 1
        count := count + 1
      if foundSemi then
        match decodeEntityBody body with
        | some replacement =>
          out := out ++ replacement
          sl := scan.drop 1
        | none =>
          out := out.push '&'
          sl := sl.drop 1
      else
        out := out.push '&'
        sl := sl.drop 1
    else
      out := out.push sl.front
      sl := sl.drop 1
  return out

/--
Percent-encode `s` for use as an HTML URL attribute. Characters in the
URL-safe set pass through; an existing `%XX` (with two hex digits) is
preserved verbatim so authors can include literal percent-escapes; all
other characters (including non-ASCII, which are encoded as their UTF-8
byte sequence) become `%HH`.
-/
def percentEncode (s : String) : String := Id.run do
  let mut sl := s.toSlice
  let mut out := ""
  while !sl.isEmpty do
    let c := sl.front
    if isUrlSafe c then
      out := out.push c
      sl := sl.drop 1
    else if c == '%' then
      let r1 := sl.drop 1
      let r2 := r1.drop 1
      match r1.front?, r2.front? with
      | some d1, some d2 =>
        if isHexDigit d1 && isHexDigit d2 then
          out := out.push '%' |>.push d1 |>.push d2
          sl := r2.drop 1
        else
          out := appendUtf8Encoded out c
          sl := r1
      | _, _ =>
        out := appendUtf8Encoded out c
        sl := sl.drop 1
    else
      out := appendUtf8Encoded out c
      sl := sl.drop 1
  return out

/--
Walks `s` and for every newline drops the leading spaces or tabs that
immediately follow it. Optionally also map newlines to spaces (used for
code-span content per CommonMark §6.1; line endings inside code spans are
treated as spaces after the §4.8 paragraph normalisation).
-/
private def normalizeContinuation (newlinesAsSpaces : Bool) (s : String) : String :=
  let (out, _) := s.foldl (init := ("", false)) fun (out, atLineStart) c =>
    if atLineStart && (c == ' ' || c == '\t') then
      (out, true)
    else if c == '\n' then
      (out.push (if newlinesAsSpaces then ' ' else '\n'), true)
    else
      (out.push c, false)
  out

private def normalizeParaText (s : String) : String :=
  normalizeContinuation false s

/--
If a code span's normalised content begins *and* ends with a space and is
not made up entirely of spaces, drop one space from each end. CommonMark
§6.1 introduces this rule so that authors can write `` ` `…` ` `` to
include content beginning or ending with a literal backtick.
-/
private def stripCodeSpanSpaces (s : String) : String :=
  let sl := s.toSlice
  if sl.startsWith ' ' && sl.endsWith ' ' && !sl.all (· == ' ') then
    (sl.drop 1 |>.dropEnd 1).toString
  else
    s

/--
Renders the verbatim contents of a code span: strips continuation-line
leading whitespace (§4.8), convert line endings to spaces (§6.1), and
remove the optional outer space pair on either side.
-/
private def renderCodeSpan (rawSrc : String) : String :=
  stripCodeSpanSpaces (normalizeContinuation true rawSrc)

/--
Flatten an inline tree to its plain-text content (CommonMark's `alt`
attribute rule for images): drop markup, keep text and code-span text,
recurse through emphasis/link/image children.
-/
partial def inlineToPlainText (source : String) (i : Inline) : String :=
  match i with
  | .text r => decodeEntities (extract source r)
  | .code _ content _ => extract source content
  | .italic _ content _ =>
    content.foldl (init := "") fun acc i => acc ++ inlineToPlainText source i
  | .bold _ content _ =>
    content.foldl (init := "") fun acc i => acc ++ inlineToPlainText source i
  | .link _ text _ _ =>
    text.foldl (init := "") fun acc i => acc ++ inlineToPlainText source i
  | .image _ _ alt _ _ =>
    alt.foldl (init := "") fun acc i => acc ++ inlineToPlainText source i
  | .hardBreak _ => "\n"
  | .autolink _ url _ _ => extract source url

/-- Renders a single inline element. -/
partial def renderInline (source : String) (i : Inline) : String :=
  match i with
  | .text r =>
    escape (decodeEntities (normalizeParaText (extract source r)))
  | .code _ content _ =>
    s!"<code>{escape (renderCodeSpan (extract source content))}</code>"
  | .italic _ content _ =>
    let inner := content.foldl (init := "") fun acc i => acc ++ renderInline source i
    s!"<em>{inner}</em>"
  | .bold _ content _ =>
    let inner := content.foldl (init := "") fun acc i => acc ++ renderInline source i
    s!"<strong>{inner}</strong>"
  | .link _ text _ target =>
    let (url, title?) := match target with
      | .inline _ url _ title? =>
        (percentEncode (decodeEntities (unescape (extract source url))),
         title?.map (fun t => decodeEntities (unescape (extract source t))))
      | .reference url title? _ =>
        (percentEncode (decodeEntities (unescape url)),
         title?.map (fun t => decodeEntities (unescape t)))
    let titleAttr := match title? with
      | some t => s!" title=\"{escape t}\""
      | none => ""
    let inner := text.foldl (init := "") fun acc i => acc ++ renderInline source i
    s!"<a href=\"{escape url}\"{titleAttr}>{inner}</a>"
  | .image _ _ alt _ target =>
    let (url, title?) := match target with
      | .inline _ url _ title? =>
        (percentEncode (decodeEntities (unescape (extract source url))),
         title?.map (fun t => decodeEntities (unescape (extract source t))))
      | .reference url title? _ =>
        (percentEncode (decodeEntities (unescape url)),
         title?.map (fun t => decodeEntities (unescape t)))
    let titleAttr := match title? with
      | some t => s!" title=\"{escape t}\""
      | none => ""
    let altText := alt.foldl (init := "") fun acc i => acc ++ inlineToPlainText source i
    s!"<img src=\"{escape url}\" alt=\"{escape altText}\"{titleAttr} />"
  | .hardBreak _ => "<br />\n"
  | .autolink _ url _ isEmail =>
    -- Autolink contents are verbatim (no backslash escapes, no entity
    -- references). The href is the raw URL percent-encoded; for email
    -- form, prefix with `mailto:`. The visible text is the URL itself,
    -- HTML-escaped only.
    let urlText := extract source url
    let href := if isEmail then "mailto:" ++ urlText else urlText
    s!"<a href=\"{escape (percentEncode href)}\">{escape urlText}</a>"

private def renderInlineArray (source : String) (inlines : Array Inline) : String :=
  inlines.foldl (init := "") fun acc i => acc ++ renderInline source i

/-- Renders an array of per-source-line inline arrays, joined by `\n`. -/
private def renderInlineLines (source : String) (lines : Array (Array Inline)) : String :=
  Id.run do
    let mut out := ""
    let mut first := true
    for line in lines do
      if first then
        first := false
      else
        out := out ++ "\n"
      out := out ++ renderInlineArray source line
    return out


/--
Strips up to `n` leading ASCII spaces from a fenced-code-block content
line. Per CommonMark §4.5, when an opening fence is indented by `n` (with
`n ≤ 3`), each content line has up to `n` leading spaces removed; lines
with fewer leading spaces are stripped down to no indent.
-/
private def stripFenceIndent (n : Nat) (line : String) : String := Id.run do
  let mut sl := line.toSlice
  let mut k := 0
  while k < n && sl.startsWith ' ' do
    sl := sl.drop 1
    k := k + 1
  return sl.toString

/-- Renders a single block element. -/
partial def renderBlock (source : String) (b : Block (Array Inline)) : String :=
  match b with
  | .paragraph lines =>
    s!"<p>{renderInlineLines source lines}</p>\n"
  | .atxHeading hashes content _closeHashes? =>
    let level := hashes.stop.byteIdx - hashes.start.byteIdx
    let inner := renderInlineArray source content
    s!"<h{level}>{inner}</h{level}>\n"
  | .setextHeading level lines _ =>
    s!"<h{level}>{renderInlineLines source lines}</h{level}>\n"
  | .fencedCode info _ _ lines =>
    let langClass := match info.infoString? with
      | some r =>
        -- Per CommonMark §4.5, only the first word of the info string is
        -- emitted as the language class; subsequent words are arbitrary
        -- metadata and are ignored for the `language-…` class. Backslash
        -- escapes and entity references in the info string are decoded
        -- (so e.g. ```` ``` foo\+bar ```` produces `class="language-foo+bar"`).
        let lang := ((extract source r).takeWhile fun c => c != ' ' && c != '\t').toString
        s!" class=\"language-{escape (decodeEntities (unescape lang))}\""
      | none => ""
    let codeContent := lines.foldl (init := "") fun acc r =>
      acc ++ escape (stripFenceIndent info.openIndent (extract source r)) ++ "\n"
    s!"<pre><code{langClass}>{codeContent}</code></pre>\n"
  | .indentedCode lines =>
    let codeContent := lines.foldl (init := "") fun acc (_, l) =>
      acc ++ escape l ++ "\n"
    s!"<pre><code>{codeContent}</code></pre>\n"
  | .blockquote _ children =>
    let inner := children.foldl (init := "") fun acc c => acc ++ renderBlock source c
    s!"<blockquote>\n{inner}</blockquote>\n"
  | .list kind tight items =>
    let (tag, attr) : String × String := match kind with
      | .bullet _ => ("ul", "")
      | .ordered start _ =>
        ("ol", if start == 1 then "" else s!" start=\"{start}\"")
    -- A tight list-item unwraps `<p>` from its direct paragraph children
    -- (CommonMark §5.3); a loose list-item renders each child via
    -- `renderBlock`, which keeps `<p>` wrappers.
    let renderItem (item : Block (Array Inline)) : String :=
      match item with
      | .listItem _ children =>
        if !tight then
          if children.isEmpty then s!"<li></li>\n"
          else
            let inner := children.foldl (init := "") fun acc c => acc ++ renderBlock source c
            s!"<li>\n{inner}</li>\n"
        else
          let body : String := Id.run do
            let mut out := ""
            let mut i : Nat := 0
            while i < children.size do
              let c := children[i]!
              match c with
              | .paragraph lines =>
                out := out ++ renderInlineLines source lines
                if i + 1 < children.size then out := out ++ "\n"
              | _ =>
                out := out ++ renderBlock source c
              i := i + 1
            return out
          let firstIsPara := children.size > 0
            && (match children[0]! with | .paragraph .. => true | _ => false)
          if children.isEmpty then s!"<li></li>\n"
          else if firstIsPara then s!"<li>{body}</li>\n"
          else s!"<li>\n{body}</li>\n"
      | _ => renderBlock source item
    let inner := items.foldl (init := "") fun acc item => acc ++ renderItem item
    s!"<{tag}{attr}>\n{inner}</{tag}>\n"
  | .listItem _ children =>
    -- A `listItem` is normally rendered by its parent list (which knows the
    -- tight/loose flag). The branch here handles the unusual case of a list
    -- item appearing outside a list.
    let inner := children.foldl (init := "") fun acc c => acc ++ renderBlock source c
    s!"<li>\n{inner}</li>\n"
  | .linkRefDef .. => ""
  | .thematicBreak _ => "<hr />\n"

/-- Renders an array of top-level blocks. -/
def renderBlocks (source : String) (blocks : Array (Block (Array Inline))) : String :=
  blocks.foldl (init := "") fun acc b => acc ++ renderBlock source b

/--
Convenience: parse `source` as a Markdown document and render it as HTML,
suitable for direct comparison with CommonMark's reference output.
-/
def renderToHtml (source : String) : String :=
  renderBlocks source (parseDocument source ⟨0⟩ source.rawEndPos)

end Lean.Server.FileWorker.Markdown.Html

structure SpecEntry where
  markdown : String
  expectedHtml : String
  sectionName : String
  exampleNum : Nat
deriving Inhabited


structure SectionStat where
  pass : Nat := 0
  total : Nat := 0
  skip : HashMap String Nat := {}
deriving Inhabited

/-- Replaces `→` (the spec's visual tab placeholder) with literal `\t`. -/
private def detab (s : String) : String :=
  s.replace "→" "\t"

/--
Whether `line` is a long-backtick fence containing the word `example`. The
spec uses 32 backticks but we accept any length ≥ 3 for robustness.
-/
private def isExampleOpenFence (line : String.Slice) : Bool :=
  line.startsWith "````````````" && line.endsWith " example"

/-- Whether `line` is the closing fence (a run of `\`` only). -/
private def isExampleCloseFence (line : String.Slice) : Bool :=
  line.startsWith "````````````" && line.all (· == '`')

/-- Returns `some` with an explanation if the test should be skipped -/
def skip? (md : String) : Option String :=
  if hasHtml md then some "HTML"
  else if (md.find? "ΑΓΩ").isSome && (md.find? "αγω").isSome then some "Unicode case-folding"
  else if (md.find? "ẞ").isSome && (md.find? "SS").isSome then some "Unicode case-folding"
  else if hasNamedEntity md then some "Named entity"
  else if hasUnicodeFlanking md then some "Unicode flanking"
  else none

where
  /--
  Whether `l` contains an HTML-tag-shaped `<…>` that's *not* a
  backslash-escaped `\<`. CommonMark backslash-escapes a `<` only when
  the preceding char is a `\` that itself isn't escaped, so we walk
  the text and skip pairs `\X` before deciding.
  -/
  hasHtml (l : String.Slice) : Bool := Id.run do
    let mut l := l
    while !l.isEmpty do
      if l.startsWith '\\' && !(l.drop 1 |>.isEmpty) then
        l := l.drop 2
      else if l.startsWith '<' ∧ !(l.drop 1).isEmpty then
        if l.drop 1 |>.startsWith Char.isAlpha then
          -- Could be an HTML tag or an autolink. Scan to the next `>`,
          -- noting whether we saw a `:` or `@` along the way and
          -- whether anything autolink-disqualifying (whitespace, `<`,
          -- newline) appeared. An autolink-shaped `<…>` is *not* HTML
          -- — the parser handles those — so we skip past it.
          let mut j := l.drop 1
          let mut hasColonOrAt := false
          let mut autolinkBroken := false
          while !j.isEmpty do
            if j.startsWith '>' then break
            if j.startsWith fun c => c == ' ' || c == '\t' || c == '\n' || c == '\r' || c == '<' then
              autolinkBroken := true; break
            if j.startsWith fun c => c == ':' || c == '@' then hasColonOrAt := true
            j := j.drop 1
          if !autolinkBroken ∧ j.startsWith '>' ∧ hasColonOrAt then
            l := j.drop 1
          else
            return true
        else if l.drop 1 |>.startsWith '?' then return true
        else if (l.drop 1).startsWith '/' && (l.drop 2).startsWith Char.isAlpha then return true
        else
          if l.drop 1 |>.startsWith '!' then
            let prefixes := #["!ELEMENT", "!DOCTYPE", "![CDATA", "!--"]
            for pre in prefixes do
              if l.drop 1 |>.startsWith pre then return true
          l := l.drop 1
      else
        l := l.drop 1
    return false
  /--
  Whether `l` contains a named HTML entity reference (`&name;`) whose
  name the renderer doesn't decode. The renderer supports
  `amp`/`lt`/`gt`/`quot`/`apos`/`nbsp` plus all numeric references —
  tests using only those run normally. Anything else (e.g. `&auml;`,
  `&copy;`) needs a full HTML5 entity table we don't carry, so we skip
  those examples.
  -/
  hasNamedEntity (l : String.Slice) : Bool := Id.run do
    let mut i := l.startPos
    while h : i ≠ l.endPos do
      if h' : i.get h == '\\' ∧ i.next h ≠ l.endPos then
        i := i.next (by grind) |>.next (by grind)
      else if i.get h == '&' ∧ (∃ (h' : i.next h ≠ l.endPos), i.next h |>.get h' |>.isAlpha) then
        let i' := i.next h
        let mut j := i'
        let mut sawSemi := false
        while h' : j ≠ l.endPos do
          let c := j.get h'
          let j' := j.next h'
          if c == ';' then sawSemi := true; break
          if !c.isAlpha && !c.isDigit then break
          j := j'
        if h' : sawSemi ∧ j > i.next h then
          let mut name := ""
          let mut k : { x : l.Pos // x ≤ j } := ⟨i.next h, by grind⟩
          while h'' : k.val < j do
            have : j ≤ l.endPos := j.le_endPos
            have : k.val ≠ l.endPos := by grind
            let k' : { x : l.Pos // x ≤ j } :=
              ⟨k.val.next (by grind), String.Slice.Pos.next_le_of_lt h''⟩
            name := name.push <| k.val.get (by grind)
            k := k'
          let supported := name == "amp" || name == "lt" || name == "gt"
            || name == "quot" || name == "apos" || name == "nbsp"
          if !supported then return true
        i := i'
      else
        i := i.next h
    return false
  /--
  Whether `l` has a `*` or `_` immediately adjacent (no intervening
  whitespace) to a non-ASCII character. CommonMark's emphasis flanking
  rule classifies the surrounding char by Unicode general category, so
  a correct verdict here would need full Pc/Pd/Pe/Pf/Pi/Po/Ps/Sc/Sk/Sm/So
  data. We don't have it, so any test that relies on classifying a
  non-ASCII char around an emphasis delimiter is skipped.
  -/
  hasUnicodeFlanking (l : String.Slice) : Bool := Id.run do
    let mut i := l.startPos
    while h : i ≠ l.endPos do
      let c := i.get h
      let i' := i.next h
      if c == '*' || c == '_' then
        if (∃ (h : i ≠ l.startPos), (i.prev h |>.get String.Slice.Pos.prev_ne_endPos).toNat ≥ 0x80) then return true
        if (∃ (h' : i.next h ≠ l.endPos), (i.next h |>.get h').toNat ≥ 0x80) then return true
      i := i'
    return false


/--
Walks the spec source line by line, extracting examples and tracking the
current section. Returns the entries in source order.
-/
private partial def extractEntries (source : String) : Array SpecEntry := Id.run do
  let lines := source.split "\n" |>.toArray
  let mut entries : Array SpecEntry := #[]
  let mut sectionName : String := ""
  let mut nextExample : Nat := 1
  let mut i : Nat := 0
  while h : i < lines.size do
    let line := lines[i]
    if line.startsWith "## " then
      sectionName := line.drop 3 |>.copy
      i := i + 1
    else if isExampleOpenFence line then
      let mut mdLines : Array String := #[]
      let mut htmlLines : Array String := #[]
      let mut sawDot := false
      let mut j := i + 1
      while hj : j < lines.size do
        let l := lines[j]
        if isExampleCloseFence l then
          break
        if l == "." && !sawDot then
          sawDot := true
        else if sawDot then
          htmlLines := htmlLines.push l.copy
        else
          mdLines := mdLines.push l.copy
        j := j + 1
      let markdown := detab ("\n".intercalate mdLines.toList ++ "\n")
      let expectedHtml := detab ("\n".intercalate htmlLines.toList
        ++ if htmlLines.isEmpty then "" else "\n")
      entries := entries.push {
        markdown, expectedHtml, sectionName, exampleNum := nextExample
      }
      nextExample := nextExample + 1
      i := j + 1
    else
      i := i + 1
  return entries

private def percent (p t : Nat) : Nat :=
  if t == 0 then 0 else (p * 100) / t

structure Opts where
  spec? : Option String := none
  section? : Option String := none
  verbose : Bool := false
  showSkipped : Bool := false

def Opts.spec (o : Opts) : String := o.spec?.getD "tests/markdown_conformance/spec.txt"

def readOpts (opts : Opts) : List String → IO Opts
  | [] => pure opts
  | "--section" :: sec :: more =>
    readOpts { opts with «section?» := some sec } more
  | "--verbose" :: more | "-v" :: more => readOpts { opts with verbose := true } more
  | "--show-skipped" :: more => readOpts { opts with showSkipped := true } more
  | spec :: more =>
    if spec.startsWith "-" then
      throw <| .userError s!"Unknown option {spec}"
    else if let some s := opts.spec? then
      throw <| .userError s!"Can't set spec to {spec} because it's already {s}"
    else
      readOpts { opts with spec? := some spec } more

public def main (args : List String) : IO UInt32 := do
  let opts ← readOpts {} args
  let path := opts.spec
  let source ← IO.FS.readFile path
  let entries := extractEntries source
  if entries.isEmpty then
    IO.eprintln s!"No examples extracted from {path}"
    return 2

  let mut stats : Std.HashMap String SectionStat := {}
  let mut allSkipped : Std.TreeMap String (Array SpecEntry) := {}
  let mut totalPass := 0
  let mut totalCount := 0
  let mut totalSkip := 0
  for entry in entries do
    if let some s := opts.section? then
      if entry.sectionName ≠ s then continue
    if let some reason := skip? entry.markdown then
      stats := stats.alter entry.sectionName fun s? =>
        let s := s?.getD {}
        some { s with skip := s.skip.alter reason (some <| ·.getD 0 + 1) }
      allSkipped := allSkipped.alter reason fun xs? =>
        xs?.getD #[] |>.push entry
      totalSkip := totalSkip + 1
    else
      let actual := Html.renderToHtml entry.markdown
      let passed := actual == entry.expectedHtml
      stats := stats.alter entry.sectionName fun s? =>
        let s := s?.getD {}
        some { s with pass := s.pass + (if passed then 1 else 0), total := s.total + 1 }
      if passed then totalPass := totalPass + 1
      if opts.verbose && !passed then
        IO.println "FAILED:"
        IO.println entry.markdown
        IO.println "EXPECTED:"
        IO.println entry.expectedHtml
        IO.println "ACTUAL:"
        IO.println actual
    totalCount := totalCount + 1

  IO.println s!"Skipped: {totalSkip}/{totalCount} ({percent totalSkip totalCount}%)"
  IO.println s!"Overall: {totalPass}/{totalCount - totalSkip} ({percent totalPass (totalCount - totalSkip)}%)"
  IO.println ""
  IO.println "Per section:"
  let sortedSections := stats.toList.mergeSort (fun a b => a.1 < b.1)
  for (name, stat) in sortedSections do
    IO.println s!"  {name}:"
    IO.println s!"    Pass: {stat.pass}/{stat.total} ({percent stat.pass stat.total}%)"
    unless stat.skip.isEmpty do
      IO.println s!"    Skip:"
      for (reason, count) in stat.skip do
        IO.println s!"      {reason}: {count}"

  if opts.showSkipped then
    IO.println s!"Skipped:"
    for h : reason in allSkipped.keys do
      have : reason ∈ allSkipped := by grind
      IO.println s!"-- {reason} --"
      for entry in allSkipped[reason] do
        let actual := Html.renderToHtml entry.markdown
        IO.println s!"SKIPPED ({reason}):"
        IO.println entry.markdown
        IO.println "EXPECTED:"
        IO.println entry.expectedHtml
        IO.println "ACTUAL:"
        IO.println actual

  return if totalPass + totalSkip == totalCount then 0 else 1
