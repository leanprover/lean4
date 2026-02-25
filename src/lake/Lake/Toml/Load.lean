/-
Copyright (c) 2024 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
module

prelude
public import Lean.Parser.Types
public import Lake.Toml.Data.Value
import Lake.Toml.Elab
import Lake.Util.Message
import Std.Do

open Lean Parser

namespace Lake.Toml

/-- Load a TOML table from some input. -/
public def loadToml (ictx : InputContext) : EIO MessageLog Table := do
  let env ←
    match (← mkEmptyEnvironment.toBaseIO) with
    | .ok env => pure env
    | .error e => throw <| MessageLog.empty.add <| mkMessageNoPos ictx <|
      m!"failed to initialize TOML environment: {e}"
  let s := toml.fn.run ictx { env, options := {} } {} (mkParserState ictx.inputString)
  if let some errorMsg := s.errorMsg then
    throw <|  MessageLog.empty.add <| mkParserErrorMessage ictx s errorMsg
  else if ictx.atEnd s.pos then
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
