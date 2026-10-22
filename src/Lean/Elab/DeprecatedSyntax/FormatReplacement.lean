/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julia M. Himmel
-/
module

prelude
public import Lean.CoreM
import Lean.Meta.TryThis
import Lean.PrettyPrinter.Formatter
import Lean.PrettyPrinter.Parenthesizer

/-!
# Printing replacements for deprecated syntax

A replacement alternative of `deprecated_syntax` turns deprecated syntax into new syntax, which is
offered as an edit of the source text of the deprecated syntax. The goal is that the edited source
parses as the new syntax, while keeping the edit as small as the source allows.

Pretty-printing the new syntax on its own does not achieve this, as the surrounding source is not
printed again: the new syntax may bind less tightly than the deprecated syntax, and its first and
last tokens may merge with the adjacent tokens of the source, e.g. `-` followed by `-1` starts a
comment. The parenthesizer and formatter avoid this when printing a whole syntax tree, but only
the deprecated syntax itself is available here, so we approximate them:

* A replacement term or tactic is parenthesized unless it binds at least as tightly as the
  deprecated syntax on both sides, in which case it parses the same in any position where the
  deprecated syntax parses. As the actual position is unknown, this can add parentheses that are
  not needed there.
* A space is inserted between the replacement and an adjacent source token if the formatter's
  token separation rule, using the current token table, requires one. The token to the left is
  recovered by lexing the preceding whitespace-delimited source text. No space is inserted before
  trivia following the deprecated syntax, nor between an identifier and a following `.`, which
  continues the identifier as field notation.

Always parenthesizing the replacement and surrounding it with spaces would be safer, but it would
change the source more than needed in most cases.

This is an incomplete heuristic, and the edited source may still parse differently from the new
syntax. For example, syntax of categories other than terms and tactics is never parenthesized, the
lexed text to the left can start inside a comment or string literal so that the wrong token is
recovered, and a replacement ending in `-` merges with a comment directly following it.
-/

namespace Lean.Elab.DeprecatedSyntax

open PrettyPrinter Parenthesizer in
/--
Returns the precedences of `stx` in category `cat`: the minimum precedence of the parsers producing
`stx`, and the minimum precedence and the category of the nested parser calls that end where `stx`
ends, if any.
-/
def syntaxPrecedences (cat : Name) (stx : Syntax) : CoreM (Option Nat × Option Nat × Name) := do
  let (_, st) ← (parenthesizeCategoryCore cat 0 {}).run { stxTrav := .fromSyntax stx }
  return (st.minPrec, st.trailPrec, st.trailCat)

/--
Whether `newStx` binds at least as tightly as `stx` on both sides in category `cat`, so that it
parses the same in any position where `stx` parses.
-/
def bindsAsTightly (cat : Name) (stx newStx : Syntax) : CoreM Bool := do
  let (minPrec, trailPrec, trailCat) ← syntaxPrecedences cat stx
  let (newMinPrec, newTrailPrec, newTrailCat) ← syntaxPrecedences cat newStx
  -- Syntax after `stx` was not absorbed by its right end, so it has precedence below `trailPrec`
  let bindsRight := match newTrailPrec, trailPrec with
    | none, _ => true
    | some newTrailPrec, some trailPrec => newTrailCat == trailCat && newTrailPrec ≥ trailPrec
    | some _, none => false
  return newMinPrec.getD 0 ≥ minPrec.getD Parser.maxPrec && bindsRight

/--
Wraps the term or tactic `newStx` in parentheses unless it binds at least as tightly as `stx`.
Other categories are left unchanged.
-/
def parenthesizeReplacement (cat : Name) (stx newStx : Syntax) : CoreM Syntax := do
  unless cat == `term || cat == `tactic do
    return newStx
  if (← try bindsAsTightly cat stx newStx catch _ => pure false) then
    return newStx
  if cat == `term then
    `(($(⟨newStx⟩)))
  else
    `(tactic| ($(⟨newStx⟩):tactic))

open PrettyPrinter.Formatter in
/-- Checks the adjacent whitespace-delimited text using the formatter's token separation rule. -/
def needsSpaceBetween (left right : String.Slice) : CoreM Bool := do
  let mut left := left.takeEndWhile (!·.isWhitespace) |>.copy
  let right := right.takeWhile (!·.isWhitespace) |>.copy
  if left.isEmpty || right.isEmpty then return false
  let table := Parser.getTokenTable (← getEnv)
  -- The left word may contain several tokens, e.g. `(-`.
  while !left.isEmpty do
    let parsed ← parseTokenCore left table
    if parsed.hasError || parsed.pos == 0 then
      -- The window can start inside a comment, string, or escaped identifier.
      left := (left.drop 1).copy
      continue
    if parsed.pos == left.rawEndPos then
      let rightParsed ← parseTokenCore right table
      let rightIdent := !rightParsed.hasError && rightParsed.stxStack.back.isIdent
      return ← needsTokenSeparator left right parsed.stxStack.back.isIdent rightIdent table
    left := (left.sliceFrom (left.pos! parsed.pos)).copy
  return false

/--
Returns the text replacing the source of `stx`, which has category `cat` and source range `range`,
by `newStx`. See the module docstring for how the text is made to fit into the surrounding source.
-/
public def formatReplacement (cat : Name) (stx newStx : Syntax) (range : Syntax.Range) :
    CoreM String := do
  let newStx ← parenthesizeReplacement cat stx newStx
  let map ← getFileMap
  let (indent, column) := Meta.Tactic.TryThis.getIndentAndColumn map range
  let suggestion : Meta.Tactic.TryThis.SuggestionText := .tsyntax (kind := cat) ⟨newStx⟩
  let mut text ← suggestion.prettyExtra (indent := indent) (column := column)
  if ← needsSpaceBetween (map.source.sliceTo (map.source.pos! range.start)) text.toSlice then
    text := " " ++ text
  -- The trailing trivia of `stx` stays in place and separates the replacement from the next token
  if stx.getTrailingSize > 0 then
    return text
  let suffix := map.source.sliceFrom (map.source.pos! range.stop)
  -- Qualified identifiers also represent field notation, which requires adjacency to `.`.
  unless cat == `term && newStx.isIdent && suffix.startsWith "." do
    if ← needsSpaceBetween text.toSlice suffix then
      text := text ++ " "
  return text

end Lean.Elab.DeprecatedSyntax
