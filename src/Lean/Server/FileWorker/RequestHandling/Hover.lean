/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Thrane Christiansen
-/

/-!

This module contains helpers used for formatting hovers according to docstring conventions. Links to
the reference manual are updated in the module Lean.DocString.Links, because that functionality is
not specific to hovers.

-/

set_option linter.missingDocs true

namespace Lean.Server.FileWorker.Hover

/--
Adds a comment marker `-- ` to a line in an output code block, respecting indentation, if the line
contains any non-space characters. Lines containing only spaces are returned unmodified.

The comment marker is always added at the indicated indentation. If the content of the line is at
least as indented, then its relative indentation is preserved. Otherwise, it's placed just after the
line comment marker.
-/
private def addCommentAt (indent : Nat) (line : String) : String := Id.run do
  if line.all (· == ' ') then return line
  let s := String.join (.replicate indent " ") ++ "-- "
  let mut iter := line.iter
  for _i in [0:indent] do
    if h : iter.hasNext then
      if iter.curr' h == ' ' then
        iter := iter.next' h
      else
        break
    else
      return s
  return s ++ iter.remainingToString

/--
Splits a string into lines, preserving newline characters
-/
private def lines (s : String) : Array String := Id.run do
  let mut result := #[]
  let mut lineStart := s.iter
  let mut iter := lineStart
  while h : iter.hasNext do
    let c := iter.curr' h
    iter := iter.next' h
    if c == '\n' then
      result := result.push <| lineStart.extract iter
      lineStart := iter

  if iter != lineStart then
    result := result.push <| lineStart.extract iter
  return result

/--
Rewrites examples in docstring Markdown for output as hover Markdown.

In particular, code blocks with the `output` class have line comment markers inserted. Editors do
not typically distinguish between code block classes, so some other visual indication is needed to
separate them. This function is not based on a compliant Markdown parser and may give unpredictable
results when used with invalid Markdown.
-/
def rewriteExamples (docstring : String) : String := Id.run do
  let lines := lines docstring
  let mut result : String := ""
  -- The current state, which tracks the context of the line being processed:
  -- * `none` means we're not in a code block
  -- * `some (none, k)` means we're in a non-output code block opened with `k` backticks
  -- * `some (some i, k)` means we're in an output code block indented `i` columns, opened with
  --   `k` backticks
  let mut inOutput : Option (Option Nat × Nat) := none
  for l in lines do
    let indent := l.takeWhile (· == ' ') |>.length
    let mut l' := l.trimLeft
    -- Is this a code block fence?
    if l'.startsWith "```" then
      let count := l'.takeWhile (· == '`') |>.length
      l' := l'.dropWhile (· == '`')
      l' := l'.dropWhile (· == ' ')
      match inOutput with
      | none => -- not in a code block
        if l'.startsWith "output" then
          inOutput := some (some indent, count)
        else
          inOutput := some (none, count)
        result := result ++ l
      | some (some i, c) => -- in an output code block
        if c == count then
          inOutput := none
          result := result ++ l
        else
          result := result ++ addCommentAt i l
      | some (none, c) => -- in a non-output code block
        if c == count then
          inOutput := none
        result := result ++ l
    else -- Current line is not a fence ("```")
      match inOutput with
      | some (some i, _c) => -- in an output code block
        -- append whitespace and comment marker
        result := result ++ addCommentAt i l
      | _ => -- Not in an output code block
        result := result ++ l
  return result
