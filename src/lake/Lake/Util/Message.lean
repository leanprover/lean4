/-
Copyright (c) 2024 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
prelude
import Lean.Message
import Lean.Exception
import Lean.Parser.Basic

open Lean Parser

namespace Lake

def mkParserErrorMessage (ictx : InputContext) (s : ParserState) (e : Parser.Error) : Message where
  fileName := ictx.fileName
  pos := ictx.fileMap.toPosition s.pos
  endPos := none
  keepFullRange := true
  data := toString e

def mkExceptionMessage (ictx : InputContext) (e : Exception) : Message where
  fileName := ictx.fileName
  pos := ictx.fileMap.toPosition <| e.getRef.getPos?.getD 0
  endPos := ictx.fileMap.toPosition <$> e.getRef.getTailPos?
  data := e.toMessageData

def mkMessageNoPos (ictx : InputContext) (data : MessageData) (severity := MessageSeverity.error) : Message where
  fileName := ictx.fileName
  pos := ictx.fileMap.toPosition 0
  endPos := none
  severity := severity
  data := data

def mkMessageStringCore
  (severity : MessageSeverity)
  (fileName caption body : String)
  (pos : Position) (endPos? : Option Position := none)
  (infoWithPos := false)
: String := Id.run do
  let mut str := body
  unless caption == "" do
    str := caption ++ ":\n" ++ str
  match severity with
  | .information =>
    if infoWithPos then
      str := mkErrorStringWithPos fileName pos (endPos := endPos?) "info: " ++ str
  | .warning =>
    str := mkErrorStringWithPos fileName pos (endPos := endPos?) "warning: " ++ str
  | .error =>
    str := mkErrorStringWithPos fileName pos (endPos := endPos?) "error: " ++ str
  if str.isEmpty || str.back != '\n' then
    str := str ++ "\n"
  return str

def mkMessageString (msg : Message) (includeEndPos := false) (infoWithPos := false) : BaseIO String := do
  let endPos? := if includeEndPos then msg.endPos else none
  match (← msg.data.toString.toBaseIO) with
  | .ok s =>
    return mkMessageStringCore msg.severity msg.fileName msg.caption s msg.pos endPos? infoWithPos
  | .error e =>
    return mkMessageStringCore .error msg.fileName msg.caption (toString e) msg.pos endPos? infoWithPos

def mkMessageLogString (log : MessageLog) : BaseIO String :=
  log.toList.foldlM (init := "") fun s m => do
    return s ++ (← mkMessageString m (infoWithPos := true))
