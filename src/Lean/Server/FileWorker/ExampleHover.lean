/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Thrane Christiansen
-/
module

prelude
public import Lean.Elab.Do

public section

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
  let s := "".pushn ' ' indent ++ "-- "
  let mut iter := line.startPos
  for _i in *...indent do
    if h : ¬iter.IsAtEnd then
      if iter.get h == ' ' then
        iter := iter.next h
      else
        -- Non-whitespace found *before* the indentation level. This output should be indented
        -- as if it were exactly at the indentation level.
        break
    else
      -- The line was entirely ' ', and was shorter than the indentation level. No `--` added.
      return line
  let remaining := line.sliceFrom iter
  if remaining.all (· == ' ') then
    return line
  else
    return s ++ remaining

/--
Splits a string into lines, preserving newline characters.
-/
private def lines (s : String) : Array String := Id.run do
  let mut result := #[]
  let mut lineStart := s.startPos
  let mut iter := lineStart
  while h : ¬iter.IsAtEnd do
    let c := iter.get h
    iter := iter.next h
    if c == '\n' then
      result := result.push <| s.extract lineStart iter
      lineStart := iter

  if iter != lineStart then
    result := result.push <| s.extract lineStart iter
  return result

private inductive RWState where
  /-- Not in a code block -/
  | normal
  /-- In a non-`output` code block opened with `ticks` backtick characters -/
  | nonOutput (ticks : Nat)
  /-- In an `output` code block indented `indent` columns opened with `ticks` backtick characters -/
  | output (indent : Nat) (ticks : Nat)

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
  -- The current state, which tracks the context of the line being processed
  let mut inOutput : RWState := .normal
  for l in lines do
    let indent := l.takeWhile (· == ' ') |>.utf8ByteSize -- this makes sense because we know the slice consists only of spaces
    let mut l' := l.trimAsciiStart
    -- Is this a code block fence?
    if l'.startsWith "```" then
      let count := l'.takeWhile (· == '`') |>.utf8ByteSize -- this makes sense because we know the slice consists only of ticks
      l' := l'.dropWhile (· == '`')
      l' := l'.dropWhile (· == ' ')
      match inOutput with
      | .normal =>
        if l'.startsWith "output" then
          inOutput := .output indent count
        else
          inOutput := .nonOutput count
        result := result ++ l
      | .output i c =>
        if c == count then
          inOutput := .normal
          result := result ++ l
        else
          result := result ++ addCommentAt i l
      | .nonOutput c =>
        if c == count then
          inOutput := .normal
        result := result ++ l
    else -- Current line is not a fence ("```")
      match inOutput with
      | .output i _c =>
        -- append whitespace and comment marker
        result := result ++ addCommentAt i l
      | _ => -- Not in an output code block
        result := result ++ l
  return result
