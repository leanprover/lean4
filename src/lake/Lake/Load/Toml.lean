/-
Copyright (c) 2024 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone, Gabriel Ebner
-/
import Lake.Toml
import Lake.Config.Package
import Lake.Util.Log

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

def mkMessage (ictx : InputContext) (data : MessageData) (severity := MessageSeverity.error) : Message where
  fileName := ictx.fileName
  pos := ictx.fileMap.toPosition 0
  endPos := none
  severity := severity
  data := data

def Toml.parseToml (ictx : InputContext) : EIO MessageLog Toml.Table := do
  let env ←
    match (← mkEmptyEnvironment.toBaseIO) with
    | .ok env => pure env
    | .error e => throw <| MessageLog.empty.add <| mkMessage ictx (toString e)
  let s := Toml.toml.fn.run ictx { env, options := {} } (getTokenTable env) (mkParserState ictx.input)
  if let some errorMsg := s.errorMsg then
    throw <|  MessageLog.empty.add <| mkParserErrorMessage ictx s errorMsg
  else if ictx.input.atEnd s.pos then
    let act := elabToml ⟨s.stxStack.back⟩
    match (← act.run {fileName := ictx.fileName, fileMap := ictx.fileMap} {env} |>.toBaseIO) with
    | .ok (t, s) =>
      if s.messages.hasErrors then
        throw s.messages
      else
        return t
    | .error e =>
      throw <| MessageLog.empty.add <| mkExceptionMessage ictx e
  else
    throw <| MessageLog.empty.add <| mkParserErrorMessage ictx s {expected := ["end of input"]}

def loadTomlConfig (dir relDir relConfigFile : FilePath) : LogIO Package := do
  let configFile := dir / relConfigFile
  let input ← IO.FS.readFile configFile
  let ictx := mkInputContext input relConfigFile.toString
  match (← Toml.parseToml ictx |>.toBaseIO) with
  | .ok val =>
    let some name := val.find? `name
      | error s!"{configFile}: configuration is missing required field 'name'"
    let .string name := name
      | error s!"{configFile}: expected name to be a string"
    return {dir, relDir, relConfigFile, config := {name}}
  | .error log =>
    log.forM fun msg => do logError (← msg.toString)
    failure
