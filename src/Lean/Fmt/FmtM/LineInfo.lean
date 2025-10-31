/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Marc Huisinga
-/
module

prelude
public import Lean.Fmt.FmtM.Error
import Init.While
import Init.Data.Slice
import Lean.Fmt.Util.Basic
public import Lean.Syntax

namespace Lean.Fmt

public structure LineInfo (s : String.Slice) where
  length : Nat
  indentation : Nat
  range : s.Subslice
deriving Inhabited

/--
For every line in `s`, determines the length of the line in characters, the level of indentation
and the range of the line (without the terminal `\n`).
-/
public def collectLineInfos (s : String.Slice) : Array (LineInfo s) := Id.run do
  let mut r := #[]
  let mut lineLength : Nat := 0
  let mut lineIndentation : Nat := 0
  let mut foundNonSpaceChar : Bool := false
  let mut lineStartPos := s.startPos
  let mut pos := s.startPos
  while h : pos ≠ s.endPos do
    let c := pos.get h
    let pos' := pos.next h
    if c == ' ' && !foundNonSpaceChar then
      lineLength := lineLength + 1
      lineIndentation := lineIndentation + 1
    else if c == '\n' then
      r :=
        r.push {
          length := lineLength
          indentation := lineIndentation
          range := s.subslice! lineStartPos pos
        }
      lineLength := 0
      lineIndentation := 0
      lineStartPos := pos'
      foundNonSpaceChar := false
    else
      lineLength := lineLength + 1
      foundNonSpaceChar := true
    pos := pos'
  r :=
    r.push {
      length := lineLength
      indentation := lineIndentation
      range := s.subslice! lineStartPos pos
    }
  return r

/-- The part of a token that lies on a single line. -/
public structure SyntaxLineToken where
  /-- Start of the token, or `none` if the token started in a previous line. -/
  startPos : String.Pos.Raw
  /-- End of the token, or `none` if the token ends in one of the next lines. -/
  endPos : String.Pos.Raw

public structure SyntaxLineInfo where
  length : Nat
  indentation : Nat
  line : String
  /-- The parts of the tokens that lie on this line, ordered by position. -/
  tokenRanges : Array Syntax.Range
  startPos : String.Pos.Raw
  endPos : String.Pos.Raw
deriving Inhabited

public instance : ToString SyntaxLineInfo where
  toString li := s!"{li.line} [{li.startPos} - {li.endPos}; #{li.length}; i{li.indentation}]"

structure collectSyntaxLineInfos.State where
  finishedLines : Array SyntaxLineInfo
  pendingLine : SyntaxLineInfo

/--
For every line in `s`, determines the length of the line in characters, the level of indentation,
the range of the line (without the terminal `\n`) and the parts of the tokens of `stx` that lie on
the line.
-/
public partial def collectSyntaxLineInfos (stx : Syntax) : Array SyntaxLineInfo :=
  let startPos := stx.getStartPos?.getD ⟨0⟩
  let (_, s) :=
    StateT.run (go stx) {
      finishedLines := #[]
      pendingLine := {
        length := 0
        indentation := 0
        line := ""
        tokenRanges := #[]
        startPos
        endPos := startPos
      }
    }
  s.finishedLines.push s.pendingLine

where

  go (stx : Syntax) : StateM collectSyntaxLineInfos.State Unit := do
    match stx with
    | .missing =>
      return
    | .atom info val =>
      if let some leading := info.getLeading?.map (·.toString) then
        advanceBy leading (isToken := false)
      advanceBy val (isToken := true)
      if let some trailing := info.getTrailing?.map (·.toString) then
        advanceBy trailing (isToken := false)
    | .ident info rawVal .. =>
      if let some leading := info.getLeading?.map (·.toString) then
        advanceBy leading (isToken := false)
      advanceBy rawVal.toString (isToken := true)
      if let some trailing := info.getTrailing?.map (·.toString) then
        advanceBy trailing (isToken := false)
    | .node _ kind args =>
      if kind == choiceKind then
        if let some firstAlternative := args[0]? then
          return ← go firstAlternative
      for arg in args do
        go arg

  advanceBy (s : String) (isToken : Bool) : StateM collectSyntaxLineInfos.State Unit := do
    let lineInfos := collectLineInfos s
    let pendingLine := (← get).pendingLine
    -- `s` is appended at the current position, which is the end of the pending line.
    let tokenStartPos := pendingLine.endPos
    let tokenEndPos := tokenStartPos.increaseBy s.utf8ByteSize
    let lineTokenRanges : Array Syntax.Range := Id.run do
      if !isToken then
        return #[]
      let token := ⟨tokenStartPos, tokenEndPos⟩
      return #[token]
    let pendingLine' := lineInfos[0]!
    let mut startPos := pendingLine.startPos
    let endPos := pendingLine.endPos.increaseBy pendingLine'.range.toSlice.utf8ByteSize
    let combinedPendingLine : SyntaxLineInfo := {
      length := pendingLine.length + pendingLine'.length
      indentation :=
        if pendingLine.indentation < pendingLine.length || isToken then
          pendingLine.indentation
        else
          pendingLine.indentation + pendingLine'.indentation
      line := pendingLine.line ++ pendingLine'.range.toString
      tokenRanges := pendingLine.tokenRanges ++ lineTokenRanges
      startPos
      endPos
    }
    let mut newLineInfos := #[combinedPendingLine]
    startPos := endPos + '\n'
    for lineInfo in lineInfos[1...*] do
      let endPos := startPos.increaseBy lineInfo.range.toSlice.utf8ByteSize
      newLineInfos :=
        newLineInfos.push {
          length := lineInfo.length
          indentation :=
            if !isToken then
              lineInfo.indentation
            else
              0
          line := lineInfo.range.toString
          tokenRanges := lineTokenRanges
          startPos
          endPos
        }
      startPos := endPos + '\n'
    let pendingLine := newLineInfos.back!
    let finishedLines := newLineInfos.pop
    modify fun s => { s with finishedLines := s.finishedLines ++ finishedLines, pendingLine }
