/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Thrane Christiansen
-/
module

prelude
public import Init.While
public import Lean.Data.Markdown.Basic
public import Lean.Data.Markdown.InlineSource
import Lean.Data.Markdown.Text

namespace Lean.Markdown

/-!
# Link Destinations and Titles

The link destination and link title grammar of CommonMark §6.3. Shared by inline links and link
reference definitions.
-/

variable {s : String.Slice}

/--
Parses a link destination at `cur`. Returns the destination and the cursor after it.

* A bracketed destination is `<`, then characters other than an unescaped `<` or `>` or a line
  ending, then `>`.
* An unbracketed destination is a sequence of characters other than ASCII whitespace and control
  characters in which parentheses balance, and it ends before a `)` that has no matching `(`. An
  unbracketed destination may be empty.
-/
public def parseLinkDestination? (cur : InlineCursor s) :
    Option (LinkDestination s × InlineCursor s) := do
  if cur.front? == some '<' then
    let openAngle ← cur.charSubslice?
    let mut cur := cur.drop1
    let urlStart := cur.startPos
    while !cur.isEmpty do
      let c := cur.front
      let curNext := cur.drop1
      if c == '\\' && Option.any isAsciiPunctuation curNext.front? then
        cur := curNext.drop1
      else if c == '>' then
        let closeAngle ← cur.charSubslice?
        let destination : LinkDestination s :=
          { angles? := some (openAngle, closeAngle), url := subsliceClamped urlStart cur.startPos }
        return (destination, curNext)
      else if c == '<' || c == '\n' || c == '\r' then
        failure
      else
        cur := curNext
    failure
  else
    let urlStart := cur.startPos
    let mut cur := cur
    let mut parenDepth : Nat := 0
    while !cur.isEmpty do
      let c := cur.front
      let curNext := cur.drop1
      if c == '\\' && Option.any isAsciiPunctuation curNext.front? then
        cur := curNext.drop1
      else if c.isWhitespace || c.toNat < 0x20 then
        break
      else if c == '(' then
        parenDepth := parenDepth + 1
        cur := curNext
      else if c == ')' then
        if parenDepth == 0 then break
        parenDepth := parenDepth - 1
        cur := curNext
      else
        cur := curNext
    guard (parenDepth == 0)
    return ({ angles? := none, url := subsliceClamped urlStart cur.startPos }, cur)

/--
Parses a link title at `cur`, which must point at its opener: `"`, `'`, or `(`. The content extends
to the first unescaped closer that matches the opener: `"`, `'`, or `)`. An unescaped `(` inside a
parenthesized title fails. Returns the title and the cursor after its closer.
-/
public def parseLinkTitle? (cur : InlineCursor s) : Option (LinkTitle s × InlineCursor s) := do
  let closerChar ← match cur.front? with
    | some '"' => some '"'
    | some '\'' => some '\''
    | some '(' => some ')'
    | _ => none
  let opener ← cur.charSubslice?
  let contentStart := opener.endExclusive
  let mut cur := cur.drop1
  while !cur.isEmpty do
    let c := cur.front
    let curNext := cur.drop1
    if c == '\\' && Option.any isAsciiPunctuation curNext.front? then
      cur := curNext.drop1
    else if c == closerChar then
      let closer ← cur.charSubslice?
      let content := cur.source.linesBetween contentStart cur.startPos
      return ({ opener, content, closer }, curNext)
    else if c == '(' && closerChar == ')' then
      failure
    else
      cur := curNext
  failure
