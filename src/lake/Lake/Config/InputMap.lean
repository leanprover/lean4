/-
Copyright (c) 2025 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
prelude
import Lake.Util.Log
import Lake.Build.Trace

open Lean System

namespace Lake

/-- Maps an input hash to a structure of artifact content hashes. -/
abbrev InputMap := Std.HashMap Hash Json

namespace InputMap

@[inline] private partial
def loadCore (h : IO.FS.Handle) (fileName : String) : LogIO InputMap := do
  let rec loop (i : Nat) (inputs : InputMap) := do
    let line ← h.getLine
    if line.isEmpty then
      return inputs
    match Json.parse line >>= fromJson? with
    | .ok (inputHash, arts) =>
      loop (i+1) (inputs.insert inputHash arts)
    | .error e =>
      logWarning s!"{fileName}: invalid JSON on line {i}: {e}"
      loop (i+1) inputs
  loop 1 {}

/-- Load an `InputMap` from a JSON Lines file. -/
def load (inputsFile : FilePath) : LogIO InputMap := do
  match (← IO.FS.Handle.mk inputsFile .read |>.toBaseIO) with
  | .ok h =>
    h.lock (exclusive := false)
    loadCore h inputsFile.toString
  | .error (.noFileOrDirectory ..) =>
    return {}
  | .error e =>
    error s!"{inputsFile}: failed to open file: {e}"

/--
Save an `InputMap` to a JSON Lines file.
Entries already in the file but not in the map will not be removed.
-/
def save (inputsFile : FilePath) (inputs : InputMap) : LogIO Unit := do
  createParentDirs inputsFile
  discard <| IO.FS.Handle.mk inputsFile .append -- ensure file exists
  match (← IO.FS.Handle.mk inputsFile .readWrite |>.toBaseIO) with
  | .ok h =>
    h.lock (exclusive := true)
    let currInputs ← loadCore h inputsFile.toString
    let newInputs := inputs.fold (fun m k v => m.insert k v) currInputs
    h.rewind
    newInputs.forM fun k v =>
       h.putStrLn (toJson (k, v)).compress
  | .error e =>
    error s!"{inputsFile}: failed to open file: {e}"
