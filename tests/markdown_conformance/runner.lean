module
import Lean.Data.Markdown
import all Lean.Data.Markdown.Parser.Inline
import Lean.Data.Json
import Std.Data.HashMap

/-!
Conformance runner for the CommonMark reference test suite.

Usage:
  lean --run tests/markdown_conformance/runner.lean [path/to/spec.txt]
  lean --run tests/markdown_conformance/runner.lean --batch documents.json

Defaults to `tests/markdown_conformance/spec.txt`. With `--batch`, the file is a JSON array of
Markdown documents, and the output is a JSON array of their HTML renderings, for comparison with a
reference implementation.

Reads the spec source directly: examples are embedded in long-backtick
fences (`````… example`), with `.` separating the markdown input from the
expected HTML output. The literal `→` character in spec.txt represents a
tab and is converted at extraction time. Section names are tracked from
`##` headings.

Each extracted example is fed through `parseDocument` and the
`Markdown.Html` renderer; the output is compared byte-for-byte against the
expected HTML. The runner prints a per-section pass/fail tally and exits 0
when every example passes, 1 when any fails, and 2 when no examples are
found.

Obtain the spec source with:

  curl -L -o tests/markdown_conformance/spec.txt \\
    https://raw.githubusercontent.com/commonmark/commonmark-spec/master/spec.txt
-/

open Std
open Lean.Markdown

/-!
## CommonMark HTML rendering (test-only)

A simple HTML renderer for the `Block` tree that `Lean.Markdown.parseDocument` produces. This lives
inside the conformance runner because nothing else in the toolchain needs it: the language server
emits semantic tokens, not HTML.

The renderer aims for byte-identical output with the CommonMark reference implementation on the
constructs we support, but does not attempt to faithfully implement the full spec. It is primarily a
conformance-suite oracle: feed Markdown to `parseDocument` plus this renderer, compare to the
expected HTML, and tally divergences.
-/

namespace Lean.Markdown.Html

variable {s : String.Slice}

private def escapeChar : Char → String
  | '&' => "&amp;"
  | '<' => "&lt;"
  | '>' => "&gt;"
  | '"' => "&quot;"
  | c   => c.toString

/-- HTML-escape `&`, `<`, `>`, and `"`. -/
def escape (s : String) : String :=
  s.foldl (init := "") fun acc c => acc ++ escapeChar c

private def hexDigit (n : Nat) : Char :=
  if n < 10 then Char.ofNat (n + '0'.toNat)
  else Char.ofNat (n - 10 + 'A'.toNat)

private def appendHex2 (out : String) (n : Nat) : String :=
  out.push '%' |>.push (hexDigit (n / 16)) |>.push (hexDigit (n % 16))

/--
Whether `c` is an ASCII character that should pass through URL percent-encoding unchanged. Matches
the cmark "safe" set that CommonMark conformance tests use: alphanumerics plus the URL-syntax
punctuation `-_.~!$&'()*+,;=:@/?#`. The `%` character is treated specially by the caller to preserve
existing percent-encoded sequences; brackets `[`/`]` and braces are *not* in the set because cmark
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
Scans `s` and for every newline drops the leading spaces or tabs that immediately follow it, per
the CommonMark §4.8 paragraph normalization.
-/
private def normalizeParaText (s : String) : String :=
  let (out, _) := s.foldl (init := ("", false)) fun (out, atLineStart) c =>
    if atLineStart && (c == ' ' || c == '\t') then
      (out, true)
    else if c == '\n' then
      (out.push '\n', true)
    else
      (out.push c, false)
  out

/-- The `title` attribute of a link or image, if its target has a title. -/
private def titleAttr (target : LinkTarget s) : String :=
  match target.title? with
  | some t => s!" title=\"{escape t.text}\""
  | none => ""

/-- Renders a single inline element. -/
partial def renderInline (i : Inline s) : String :=
  match i with
  | .text r =>
    escape (normalizeParaText r.copy)
  | .code _ content _ =>
    s!"<code>{escape content.text}</code>"
  | .math _ content _ display =>
    -- The element and attribute that md4c's HTML renderer emits, for comparison with it.
    let type := if display then " type=\"display\"" else ""
    s!"<x-equation{type}>{escape content.text}</x-equation>"
  | .italic _ content _ =>
    let inner := content.foldl (init := "") fun acc i => acc ++ renderInline i
    s!"<em>{inner}</em>"
  | .bold _ content _ =>
    let inner := content.foldl (init := "") fun acc i => acc ++ renderInline i
    s!"<strong>{inner}</strong>"
  | .link _ text _ target =>
    let inner := text.foldl (init := "") fun acc i => acc ++ renderInline i
    s!"<a href=\"{escape (percentEncode target.destination.text)}\"{titleAttr target}>{inner}</a>"
  | .image _ _ alt _ target =>
    s!"<img src=\"{escape (percentEncode target.destination.text)}\" alt=\"{escape (Inline.plainText alt)}\"{titleAttr target} />"
  | .hardBreak _ _ => "<br />\n"
  | .autolink _ url _ isEmail =>
    -- Autolink contents are verbatim (no backslash escapes, no entity
    -- references). The href is the raw URL percent-encoded; for email
    -- form, prefix with `mailto:`. The visible text is the URL itself,
    -- HTML-escaped only.
    let urlText := url.copy
    let href := if isEmail then "mailto:" ++ urlText else urlText
    s!"<a href=\"{escape (percentEncode href)}\">{escape urlText}</a>"
  | .softBreak _ => "\n"
  | .html lines => lines.text
  | .escape _ char => escape char.copy
  | .entity _ value => escape value

private def renderInlineArray (inlines : Array (Inline s)) : String :=
  inlines.foldl (init := "") fun acc i => acc ++ renderInline i

/-- Renders a single block element. -/
partial def renderBlock (b : Block s) : String :=
  match b with
  | .paragraph content =>
    s!"<p>{renderInlineArray content}</p>\n"
  | .atxHeading level _hashes content _closeHashes? =>
    let inner := renderInlineArray content
    s!"<h{level}>{inner}</h{level}>\n"
  | .setextHeading level content _ =>
    s!"<h{level}>{renderInlineArray content}</h{level}>\n"
  | .fencedCode info _ _ lines =>
    let langClass := match info.infoString? with
      | some r =>
        -- Per CommonMark §4.5, only the first word of the info string is
        -- emitted as the language class; subsequent words are arbitrary
        -- metadata and are ignored for the `language-…` class. Backslash
        -- escapes and entity references in the info string are decoded
        -- (so e.g. ```` ``` foo\+bar ```` produces `class="language-foo+bar"`).
        let lang := (r.copy.takeWhile fun c => c != ' ' && c != '\t').toString
        s!" class=\"language-{escape (decodeText lang)}\""
      | none => ""
    let codeContent := lines.foldl (init := "") fun acc line =>
      acc ++ escape line.text ++ "\n"
    s!"<pre><code{langClass}>{codeContent}</code></pre>\n"
  | .indentedCode lines =>
    let codeContent := lines.foldl (init := "") fun acc line =>
      acc ++ escape line.text ++ "\n"
    s!"<pre><code>{codeContent}</code></pre>\n"
  | .blockquote _ children =>
    let inner := children.foldl (init := "") fun acc c => acc ++ renderBlock c
    s!"<blockquote>\n{inner}</blockquote>\n"
  | .list kind tight items =>
    let (tag, attr) : String × String := match kind with
      | .bullet _ => ("ul", "")
      | .ordered start _ =>
        ("ol", if start == 1 then "" else s!" start=\"{start}\"")
    -- A tight list-item unwraps `<p>` from its direct paragraph children
    -- (CommonMark §5.3); a loose list-item renders each child via
    -- `renderBlock`, which keeps `<p>` wrappers.
    let renderItem (item : Block s) : String :=
      match item with
      | .listItem _ children =>
        if !tight then
          let inner := children.foldl (init := "") fun acc c => acc ++ renderBlock c
          if inner.isEmpty then s!"<li></li>\n" else s!"<li>\n{inner}</li>\n"
        else
          let body : String := Id.run do
            let mut out := ""
            let mut i : Nat := 0
            while i < children.size do
              let c := children[i]!
              match c with
              | .paragraph content =>
                out := out ++ renderInlineArray content
                if i + 1 < children.size then out := out ++ "\n"
              | _ =>
                out := out ++ renderBlock c
              i := i + 1
            return out
          -- Reference definitions render as nothing, so the first rendered child decides.
          let firstIsPara :=
            match children.find? (fun | .linkRefDef .. => false | _ => true) with
            | some (.paragraph ..) => true
            | _ => false
          if body.isEmpty then s!"<li></li>\n"
          else if firstIsPara then s!"<li>{body}</li>\n"
          else s!"<li>\n{body}</li>\n"
      | _ => renderBlock item
    let inner := items.foldl (init := "") fun acc item => acc ++ renderItem item
    s!"<{tag}{attr}>\n{inner}</{tag}>\n"
  | .listItem _ children =>
    -- A `listItem` is normally rendered by its parent list (which knows the
    -- tight/loose flag). The branch here handles the unusual case of a list
    -- item that appears outside a list.
    let inner := children.foldl (init := "") fun acc c => acc ++ renderBlock c
    s!"<li>\n{inner}</li>\n"
  | .linkRefDef .. => ""
  | .thematicBreak _ => "<hr />\n"
  | .html lines => "\n".intercalate (lines.toList.map (·.text)) ++ "\n"

/-- Renders an array of top-level blocks. -/
def renderBlocks (blocks : Array (Block s)) : String :=
  blocks.foldl (init := "") fun acc b => acc ++ renderBlock b

/--
Convenience: parse `source` as a Markdown document and render it as HTML,
suitable for direct comparison with CommonMark's reference output.
-/
def renderToHtml (source : String) (extensions : Extensions := {}) : String :=
  renderBlocks (parseDocument source.toSlice (extensions := extensions))

end Lean.Markdown.Html

structure SpecEntry where
  markdown : String
  expectedHtml : String
  sectionName : String
  exampleNum : Nat
deriving Inhabited


structure SectionStat where
  pass : Nat := 0
  total : Nat := 0
deriving Inhabited

/-- Replaces `→` (the spec's visual tab placeholder) with literal `\t`. -/
private def detab (s : String) : String :=
  s.replace "→" "\t"

/--
Whether `line` is a long-backtick fence that contains the word `example`. The
spec uses 32 backticks; a fence of at least 12 is accepted.
-/
private def isExampleOpenFence (line : String.Slice) : Bool :=
  line.startsWith "````````````" && line.endsWith " example"

/-- Whether `line` is the closing fence (a sequence of backticks only). -/
private def isExampleCloseFence (line : String.Slice) : Bool :=
  line.startsWith "````````````" && line.all (· == '`')

/--
Reads the spec source line by line, extracting examples and tracking the
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
  /-- A JSON array of documents to render instead of running the suite. -/
  batch? : Option String := none
  /-- Whether to enable the `latexMath` extension when rendering a batch. -/
  math : Bool := false

def Opts.spec (o : Opts) : String := o.spec?.getD "tests/markdown_conformance/spec.txt"

def readOpts (opts : Opts) : List String → IO Opts
  | [] => pure opts
  | "--section" :: sec :: more =>
    readOpts { opts with «section?» := some sec } more
  | "--verbose" :: more | "-v" :: more => readOpts { opts with verbose := true } more
  | "--batch" :: path :: more => readOpts { opts with batch? := some path } more
  | "--math" :: more => readOpts { opts with math := true } more
  | spec :: more =>
    if spec.startsWith "-" then
      throw <| .userError s!"Unknown option {spec}"
    else if let some s := opts.spec? then
      throw <| .userError s!"Can't set spec to {spec} because it's already {s}"
    else
      readOpts { opts with spec? := some spec } more

/--
Renders each document of the JSON array in the file at `path` and prints the renderings as a JSON
array.
-/
def runBatch (path : String) (extensions : Extensions) : IO UInt32 := do
  let source ← IO.FS.readFile path
  match Lean.Json.parse source >>= (·.getArr?) with
  | .error e =>
    IO.eprintln s!"{path}: {e}"
    return 2
  | .ok docs =>
    let mut renderings : Array Lean.Json := #[]
    for doc in docs do
      match doc.getStr? with
      | .error e =>
        IO.eprintln s!"{path}: {e}"
        return 2
      | .ok md => renderings := renderings.push (Lean.Json.str (Html.renderToHtml md extensions))
    IO.println (Lean.Json.arr renderings).compress
    return 0

public def main (args : List String) : IO UInt32 := do
  let opts ← readOpts {} args
  if let some path := opts.batch? then return ← runBatch path { latexMath := opts.math }
  let path := opts.spec
  let source ← IO.FS.readFile path
  let entries := extractEntries source
  if entries.isEmpty then
    IO.eprintln s!"No examples extracted from {path}"
    return 2

  let mut stats : Std.HashMap String SectionStat := {}
  let mut totalPass := 0
  let mut totalCount := 0
  for entry in entries do
    if let some s := opts.section? then
      if entry.sectionName ≠ s then continue
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

  IO.println s!"Overall: {totalPass}/{totalCount} ({percent totalPass totalCount}%)"
  IO.println ""
  IO.println "Per section:"
  let sortedSections := stats.toList.mergeSort (fun a b => a.1 < b.1)
  for (name, stat) in sortedSections do
    IO.println s!"  {name}:"
    IO.println s!"    Pass: {stat.pass}/{stat.total} ({percent stat.pass stat.total}%)"

  return if totalPass == totalCount then 0 else 1
