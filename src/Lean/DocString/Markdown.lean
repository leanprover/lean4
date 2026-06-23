/-
Copyright (c) 2023-2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Thrane Christiansen
-/

module

prelude

public import Lean.DocString.Types
public import Init.Data.String.TakeDrop
public import Init.Data.String.Search
public import Init.Data.String.Length
import Init.Data.ToString.Macro
import Init.While

set_option linter.missingDocs true

namespace Lean.Doc

/--
A monad for accumulating footnotes while rendering Markdown. Footnote labels are paired with their
already-rendered bodies, in order of first reference. `MarkdownM.run'` flushes them at the end of
the document.
-/
public abbrev MarkdownM := StateM (Array (String × String))

namespace MarkdownM

/--
Tracks which inline delimiters are already open so that nested `*` / `**` / `[…](…)` don't emit
redundant openers and closers.
-/
public structure InlineCtx where
  /-- The current code is inside emphasis (`*…*`). -/
  inEmph : Bool := false
  /-- The current code is inside strong emphasis (`**…**`). -/
  inBold : Bool := false
  /-- The current code is inside a link's display text. -/
  inLink : Bool := false
deriving Inhabited

end MarkdownM

open MarkdownM in
/--
Renders an action that produces an array of lines into a single Markdown string, appending any
accumulated footnotes after the main body.
-/
public def MarkdownM.run' (act : MarkdownM (Array String)) : String :=
  let (lines, footnotes) := act #[]
  let main := "\n".intercalate lines.toList
  if footnotes.isEmpty then
    main
  else
    let foots := footnotes.toList.map fun (n, t) => s!"[^{n}]:{t}"
    main ++ "\n\n" ++ "\n\n".intercalate foots

/--
Drops trailing ASCII spaces (`' '`) from a string. Used to compute the "empty line" form of a
per-line prefix (`"> "` becomes `">"`) so that prefixed empty lines don't carry trailing whitespace
into the rendered output.
-/
def trimEndSpaces (s : String) : String :=
  s.dropEndWhile ' ' |>.copy

/--
Applies a uniform prefix to every line. Empty lines receive the trimmed prefix to avoid trailing
whitespace (which denotes a hard line break).
-/
public def prefixLines (p : String) (lines : Array String) : Array String :=
  let pTrim := trimEndSpaces p
  lines.map fun l => if l.isEmpty then pTrim else p ++ l

/--
Applies one prefix to the first line and a different prefix to subsequent lines. Used for list items,
where the first line gets `"* "` / `"1. "` and the continuation lines get `"  "` / `"   "`.
-/
public def prefixListLines (head rest : String) (lines : Array String) : Array String :=
  let headTrim := trimEndSpaces head
  let restTrim := trimEndSpaces rest
  lines.mapIdx fun i l =>
    let (p, pTrim) := if i = 0 then (head, headTrim) else (rest, restTrim)
    if l.isEmpty then pTrim else p ++ l

/--
Concatenates an array of "block" line arrays into one line array, with a single empty separator line
between adjacent non-empty blocks. Empty input blocks are skipped.
-/
public def joinBlocks (blocks : Array (Array String)) : Array String :=
  blocks.foldl (init := #[]) fun acc b =>
    if b.isEmpty then acc
    else if acc.isEmpty then b
    else acc.push "" ++ b

/--
Concatenates two strings that are the result of rendering consecutive inliens, inserting a U+200B
zero-width space when both concatenated ends are backticks. Markdown has no syntactic way to place
two code spans consecutively, so the zero-width space disambiguates them without introducing visible
whitespace.
-/
def glueInlineBoundary (l r : String) : String :=
  if l.endsWith "`" ∧ r.startsWith "`" then l ++ "​" ++ r
  else l ++ r

/--
Concatenates a array of lines, where each line is an array of rendered inlines. The last line of one
piece is glued onto the first line of the next via `glueInlineBoundary` (so `.text "a"` followed by
`.text "b"` yields one line `"ab"`, but two adjacent `.code` spans get a U+200B between them).
-/
public def joinInlines (parts : Array (Array String)) : Array String :=
  parts.foldl (init := #[]) fun acc next =>
    if h : next.size = 0 then acc
    else if h' : acc.size = 0 then next
    else
      let lastIdx := acc.size - 1
      have : 0 < acc.size := Nat.ne_zero_iff_zero_lt.mp h'
      have : 0 < next.size := Nat.ne_zero_iff_zero_lt.mp h
      have : lastIdx < acc.size := Nat.sub_one_lt h'
      let glued := glueInlineBoundary (acc[lastIdx]) next[0]
      acc.set lastIdx glued ++ next.drop 1

/--
A means of transforming values into Markdown lines.
-/
public class ToMarkdown (α : Type u) where
  /--
  Render an `α` to its Markdown lines. The lines should not contain literal `\n`
  characters; line breaks are encoded by the array structure.
  -/
  toMarkdown : α → MarkdownM (Array String)

/--
A way to transform inline elements extended with `i` into Markdown lines.
-/
public class MarkdownInline (i : Type u) where
  /--
  Render the `i` and its contents to Markdown lines, given a recursive renderer
  for ordinary inline content.
  -/
  toMarkdown :
    (Inline i → MarkdownM (Array String)) → i → Array (Inline i) →
    MarkdownM (Array String)

public instance : MarkdownInline Empty where
  toMarkdown := nofun

/--
A way to transform block elements extended with `b` (containing inline elements
extended with `i`) into Markdown lines.
-/
public class MarkdownBlock (i : Type u) (b : Type v) where
  /--
  Render the `b` and its contents to Markdown lines, given recursive renderers
  for inline and block content.
  -/
  toMarkdown :
    (Inline i → MarkdownM (Array String)) → (Block i b → MarkdownM (Array String)) →
    b → Array (Block i b) → MarkdownM (Array String)

public instance : MarkdownBlock i Empty where
  toMarkdown := nofun

/--
Checks whether `c` needs escaping in a context that definitely cannot start a block. `next?` is the
following character, used for the `![…]` image-syntax check.
-/
def midLineSpecial (c : Char) (next? : Option Char) : Bool :=
  match c with
  | '!' => next? == some '['
  | _   => "*_`<[]{}()#".any c

/--
Checks whether `c` needs escaping in a context that could potentially start a block. In these
contexts, potential list and blockquote markers need escaping.
-/
def markerPrefixSpecial (prev? : Option Char) (c : Char) (next? : Option Char) : Bool :=
  let endsMarker := next? == some ' ' || next?.isNone
  match c with
  | '>' => true
  | '-' | '+' => endsMarker
  | '.' => prev?.any (·.isDigit) && endsMarker
  | _ => midLineSpecial c next?

/--
Backslash-escapes Markdown-significant punctuation in `s` so it renders as literal text. `s` must
be a single line.
-/
def escape (s : String) : String := Id.run do
  let mut s' := ""
  let mut iter := s.startPos
  let mut prev? : Option Char := none
  -- First, escape everything that could start a block, until that's definitely impossible.
  while h : ¬iter.IsAtEnd do
    let c := iter.get h
    let nextIter := iter.next h
    let next? : Option Char :=
      if h' : ¬nextIter.IsAtEnd then some (nextIter.get h') else none
    if markerPrefixSpecial prev? c next? then
      s' := s'.push '\\'
    s' := s'.push c
    prev? := some c
    iter := nextIter
    unless c.isDigit || "> -+. \t".any c do
      break
  -- Now escape more conservatively. prev? is no longer used.
  while h : ¬iter.IsAtEnd do
    let c := iter.get h
    let nextIter := iter.next h
    let next? : Option Char :=
      if h' : ¬nextIter.IsAtEnd then some (nextIter.get h') else none
    if midLineSpecial c next? then
      s' := s'.push '\\'
    s' := s'.push c
    iter := nextIter
  return s'

/--
Length of the longest unbroken run of `` ` `` characters in `str`.
-/
def longestBacktickRun (str : String) : Nat := Id.run do
  let mut longest := 0
  let mut current := 0
  let mut iter := str.startPos
  while h : ¬iter.IsAtEnd do
    let c := iter.get h
    iter := iter.next h
    if c == '`' then
      current := current + 1
    else
      longest := max longest current
      current := 0
  return max longest current

/--
A run of `` ` `` characters one longer than any run inside `str` (with a minimum of `atLeast`),
suitable for use as a code block fence or a delimiter for inline code.
-/
def fenceFor (atLeast : Nat) (str : String) : String :=
  "".pushn '`' (max atLeast (longestBacktickRun str) + 1)

def quoteCode (str : String) : String :=
  let backticks := fenceFor 0 str
  let str := if str.startsWith "`" || str.endsWith "`" then " " ++ str ++ " " else str
  backticks ++ str ++ backticks

/--
Splits a string into an array of lines on `'\n'`, retaining empty trailing/leading lines (so
`"a\nb\n"` yields `#["a", "b", ""]`). Used to convert code blocks into the line-array representation
used by the rest of the renderer.
-/
def splitNewlines (str : String) : Array String :=
  str.split '\n' |>.map (·.copy) |>.toArray

/--
Produces a fenced code block as a line array (with no surrounding blank lines), with a sufficiently
long fence.
-/
def codeBlockLines (str : String) : Array String := Id.run do
  let fence := fenceFor 2 str
  let body := splitNewlines str
  -- Drop a trailing empty so the closing fence isn't preceded by a blank line.
  let body := if body.size > 0 && body.back!.isEmpty then body.pop else body
  #[fence] ++ body ++ #[fence]

/--
Splits off the leading run of whitespace from an inline tree, returning the whitespace as a plain
string and the remainder as a new inline. This allows emphasis to be applied to strings that start
or end with whitespace, taking the flanking rules of Markdown into account.
-/
partial def trimLeft (inline : Inline i) : (String × Inline i) := go [inline]
where
  go : List (Inline i) → String × Inline i
    | [] => ("", .empty)
    | .text s :: more =>
      if s.all Char.isWhitespace then
        let (pre, post) := go more
        (s ++ pre, post)
      else
        let afterWhitespace := s.skipPrefixWhile Char.isWhitespace
        let s1 := s.sliceTo afterWhitespace |>.copy
        let s2 := s.sliceFrom afterWhitespace |>.copy
        (s1, .text s2 ++ .concat more.toArray)
    | .concat xs :: more => go (xs.toList ++ more)
    | here :: more => ("", here ++ .concat more.toArray)

/--
Splits off the trailing run of whitespace from an inline tree, returning the remainder as a new
inline and the whitespace as a plain string. This allows emphasis to be applied to strings that
start or end with whitespace, taking the flanking rules of Markdown into account.
-/
partial def trimRight (inline : Inline i) : (Inline i × String) := go #[inline]
where
  go (xs : Array (Inline i)) : Inline i × String :=
    if h : xs.size = 0 then (.empty, "")
    else
      match xs.back (Nat.ne_zero_iff_zero_lt.mp h) with
      | .text s =>
        if s.all Char.isWhitespace then
          let (pre, post) := go xs.pop
          (pre, post ++ s)
        else
          let pos := s.skipSuffixWhile Char.isWhitespace
          let ws := s.sliceFrom pos
          let nonWs := s.sliceTo pos
          (.concat (xs.pop.push (.text nonWs.copy)), ws.copy)
      | .concat ys => go (xs.pop ++ ys)
      | _ => (.concat xs, "")


/--
Strips leading and trailing whitespace from `inline`, returning the leading whitespace, the stripped
middle (still an `Inline`), and the trailing whitespace, in order. The caller can then re-emit the
leading and trailing whitespace *outside* of emphasis.
-/
def trim (inline : Inline i) : (String × Inline i × String) :=
  let (pre, more) := trimLeft inline
  let (mid, post) := trimRight more
  (pre, mid, post)

open MarkdownM in
/--
Renders an `Inline i` to its Markdown lines. The `InlineCtx` argument tracks which inline delimiters
are already open so that nested `*` / `**` / `[…](…)` don't emit redundant openers and closers. The
top level is represented by `{}`.
-/
partial def inlineMarkdown [MarkdownInline i] :
    InlineCtx → Inline i → MarkdownM (Array String)
  | _, .text s => return #[escape s]
  | _, .linebreak _ => return #["", ""]
  | ctx, .emph xs => do
    let (pre, mid, post) := trim (.concat xs)
    let inner ← inlineMarkdown { ctx with inEmph := true } mid
    let mut pieces : Array (Array String) := #[]
    if !pre.isEmpty then pieces := pieces.push #[pre]
    if !ctx.inEmph then pieces := pieces.push #["*"]
    pieces := pieces.push inner
    if !ctx.inEmph then pieces := pieces.push #["*"]
    if !post.isEmpty then pieces := pieces.push #[post]
    return joinInlines pieces
  | ctx, .bold xs => do
    let (pre, mid, post) := trim (.concat xs)
    let inner ← inlineMarkdown { ctx with inBold := true } mid
    let mut pieces : Array (Array String) := #[]
    if !pre.isEmpty then pieces := pieces.push #[pre]
    if !ctx.inBold then pieces := pieces.push #["**"]
    pieces := pieces.push inner
    if !ctx.inBold then pieces := pieces.push #["**"]
    if !post.isEmpty then pieces := pieces.push #[post]
    return joinInlines pieces
  | ctx, .concat xs => do
    let parts ← xs.mapM (inlineMarkdown ctx)
    return joinInlines parts
  | ctx, .link content url => do
    if ctx.inLink then
      let parts ← content.mapM (inlineMarkdown ctx)
      return joinInlines parts
    else
      let inner ← inlineMarkdown { ctx with inLink := true } (.concat content)
      return joinInlines #[#["["], inner, #["](" ++ url ++ ")"]]
  | _, .image alt url => return #[s!"![{escape alt}]({url})"]
  | ctx, .footnote name content => do
    let parts ← content.mapM (inlineMarkdown ctx)
    let footnoteContent := "\n".intercalate (joinInlines parts).toList
    modify (·.push (name, footnoteContent))
    return #[s!"[^{name}]"]
  | _, .code str => return #[quoteCode str]
  | _, .math .display m => return #[s!"$${m}$$"]
  | _, .math .inline m => return #[s!"${m}$"]
  | ctx, .other container content =>
    MarkdownInline.toMarkdown (inlineMarkdown ctx) container content

public instance [MarkdownInline i] : ToMarkdown (Inline i) where
  toMarkdown := private inlineMarkdown {}

partial def blockMarkdown [MarkdownInline i] [MarkdownBlock i b] :
    Block i b → MarkdownM (Array String)
  | .para xs => inlineMarkdown {} (.concat xs)
  | .concat bs => do
    let parts ← bs.mapM blockMarkdown
    return joinBlocks parts
  | .blockquote bs => do
    let parts ← bs.mapM blockMarkdown
    return prefixLines "> " (joinBlocks parts)
  | .ul items => do
    let rendered ← items.mapM fun item => do
      let inner ← item.contents.mapM blockMarkdown
      return prefixListLines "* " "  " (joinBlocks inner)
    return joinBlocks rendered
  | .ol start items => do
    let mut out : Array (Array String) := #[]
    let mut n := max 1 start.toNat
    for item in items do
      let head := s!"{n}. "
      let cont := "".pushn ' ' head.utf8ByteSize
      let inner ← item.contents.mapM blockMarkdown
      out := out.push (prefixListLines head cont (joinBlocks inner))
      n := n + 1
    return joinBlocks out
  | .dl items => do
    let rendered ← items.mapM fun item => do
      let term ← inlineMarkdown {} (.bold item.term)
      let desc ← item.desc.mapM blockMarkdown
      let termWithColon := joinInlines #[term, #[":"]]
      -- Single-block descriptions are attached directly to the term. Multi-block descriptions are
      -- separated from the term with a blank line so the term doesn't fuse into the
      -- first description paragraph.
      let body :=
        if item.desc.size ≤ 1 then termWithColon ++ joinBlocks desc
        else joinBlocks (#[termWithColon] ++ desc)
      return prefixListLines "* " "  " body
    return joinBlocks rendered
  | .code str => return codeBlockLines str
  | .other container content =>
    MarkdownBlock.toMarkdown (i := i) (b := b) (inlineMarkdown {}) blockMarkdown container content

public instance [MarkdownInline i] [MarkdownBlock i b] : ToMarkdown (Block i b) where
  toMarkdown := private blockMarkdown

/--
Renders a `Part` (a logical document section) at the given heading level. Headings use ATX-style
(`#`, `##`, …) with level `0` rendering as `#`.
-/
public partial def partMarkdown [MarkdownInline i] [MarkdownBlock i b] (level : Nat)
    (part : Part i b p) : MarkdownM (Array String) := do
  let titleParts ← part.title.mapM ToMarkdown.toMarkdown
  let header := "".pushn '#' (level + 1) ++ " "
  let titleLine := joinInlines (#[#[header]] ++ titleParts)
  let contentBlocks ← part.content.mapM ToMarkdown.toMarkdown
  let subPartBlocks ← part.subParts.mapM (partMarkdown (level + 1))
  return joinBlocks (#[titleLine] ++ contentBlocks ++ subPartBlocks)

public instance [MarkdownInline i] [MarkdownBlock i b] : ToMarkdown (Part i b p) where
  toMarkdown part := partMarkdown 0 part
