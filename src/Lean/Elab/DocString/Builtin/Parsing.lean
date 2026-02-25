/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module
prelude
public import Lean.Parser.Extension
public import Init.While
import Init.Data.Array.Attach
import Init.Data.Array.Mem

namespace Lean.Doc
open Lean.Parser

public section

private def strLitRange [Monad m] [MonadFileMap m] (s : StrLit) : m Lean.Syntax.Range := do
  let pos := (s.raw.getPos? (canonicalOnly := true)).get!
  let endPos := s.raw.getTailPos? true |>.get!
  return ⟨pos, endPos⟩

variable [Monad m] [MonadFileMap m] [MonadEnv m]
variable [MonadError m] [AddMessageContext m] [MonadLog m] [MonadOptions m]

def parseStrLit (p : ParserFn) (s : StrLit) : m Syntax := do
  let text ← getFileMap
  let env ← getEnv
  let ⟨pos, endPos⟩ ← strLitRange s
  let endPos := if endPos ≤ text.source.rawEndPos then endPos else text.source.rawEndPos
  let ictx :=
    mkInputContext text.source (← getFileName)
      (endPos := endPos) (endPos_valid := by simp only [endPos]; split <;> simp [*])
  -- TODO fallback for non-original syntax
  let s := (mkParserState text.source).setPos pos
  let s := p.run ictx { env, options := ← getOptions } (getTokenTable env) s

  if !s.allErrors.isEmpty  then
    throwError (s.toErrorMsg ictx)
  else if ictx.atEnd s.pos then
    pure s.stxStack.back
  else
    throwError ((s.mkError "end of input").toErrorMsg ictx)

def parseQuotedStrLit (p : ParserFn) (strLit : StrLit) : m Syntax := do
  let text ← getFileMap
  let env ← getEnv
  let ⟨pos, _⟩ ← strLitRange strLit
  let pos ← do
    let mut pos := pos
    if pos.get text.source == 'r' then
      pos := pos.next text.source
      while pos.get text.source == '#' do
        pos := pos.next text.source
    if pos.get text.source == '"' then
      pure <| pos.next text.source
    else
      throwErrorAt strLit "Not a quoted string literal"
  let str := strLit.getString
  let ictx := mkInputContext str (← getFileName)
  let s := mkParserState str
  let s := p.run ictx { env, options := ← getOptions } (getTokenTable env) s

  if !s.allErrors.isEmpty then
    let s := { s with
        pos := reposition text pos str s.pos
        recoveredErrors := s.recoveredErrors.map fun
        | (ePos, stk, err) => (reposition text pos str ePos, stk, err)
        errorMsg := s.errorMsg.map fun (e : Error) =>
          { e with unexpectedTk := repositionSyntax text pos str e.unexpectedTk }
      }
    throwError (s.toErrorMsg ictx)
  else if ictx.atEnd s.pos then
    pure <| repositionSyntax text pos str s.stxStack.back
  else
    throwError ((s.mkError "end of input").toErrorMsg ictx)
where
  reposition (text : FileMap) (posOfStr : String.Pos.Raw) (str : String) (posInStr : String.Pos.Raw) : String.Pos.Raw :=
    nextn text.source (posIndex str posInStr) posOfStr
  repositionSyntax (text : FileMap) (posOfStr : String.Pos.Raw) (str : String) : Syntax → Syntax
    | .node info k args => .node (repositionInfo text posOfStr str info) k (args.map (repositionSyntax text posOfStr str))
    | .ident info sub x pre => .ident (repositionInfo text posOfStr str info) sub x pre
    | .atom info s => .atom (repositionInfo text posOfStr str info) s
    | .missing => .missing
  repositionInfo (text : FileMap) (posOfStr : String.Pos.Raw) (str : String) : SourceInfo → SourceInfo
    | .original _ pos _ endPos =>
      .synthetic (reposition text posOfStr str pos) (reposition text posOfStr str endPos) true
    | .synthetic pos endPos c =>
      .synthetic (reposition text posOfStr str pos) (reposition text posOfStr str endPos) c
    | .none => .none

  nextn (str : String) (n : Nat) (p : String.Pos.Raw) : String.Pos.Raw :=
    n.fold (init := p) fun _ _ _ => p.next str
  posIndex (str : String) (p : String.Pos.Raw) : Nat := Id.run do
    let mut p := p
    let mut n := 0
    while p > 0 do
      p := p.prev str
      n := n + 1
    return n

def parseStrLit' (p : ParserFn) (s : StrLit) : m (Syntax × Bool) := do
  let text ← getFileMap
  let env ← getEnv
  let endPos := s.raw.getTailPos? true |>.get!
  let endPos := if endPos ≤ text.source.rawEndPos then endPos else text.source.rawEndPos
  let ictx :=
    mkInputContext text.source (← getFileName)
      (endPos := endPos) (endPos_valid := by simp only [endPos]; split <;> simp [*])
  -- TODO fallback for non-original syntax
  let s := (mkParserState text.source).setPos (s.raw.getPos? (canonicalOnly := true)).get!
  let s := p.run ictx { env, options := ← getOptions } (getTokenTable env) s

  let err ←
    if !s.allErrors.isEmpty then
      logError (s.toErrorMsg ictx)
      pure true
    else if !ictx.atEnd s.pos then
      logError ((s.mkError "end of input").toErrorMsg ictx)
      pure true
    else pure false
  pure (s.stxStack.back, err)
