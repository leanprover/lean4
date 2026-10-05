/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

prelude
public import Init.System.IO
import Lean.Data.Json
import Lean.Compiler.NameDemangling
import Lake.Util.IO
import Lake.Util.Url
import Init.Data.String.Extra
import Init.Data.String.Search
import Init.Data.String.TakeDrop
import Init.System.Uri
import Init.While

/-!
# `lake samply`

Profile a Lean executable with [samply](https://github.com/mstange/samply)
and demangle Lean names for [Firefox Profiler](https://profiler.firefox.com).
-/

namespace Lake.Samply

open Lean (Json toJson)

/-- Check that a command is available on PATH. -/
private def requireCmd (cmd : String) (installHint : String) : IO Unit := do
  let result ← IO.Process.output { cmd := "sh", args := #["-c", s!"command -v {cmd}"] }
  if result.exitCode != 0 then
    throw <| IO.userError s!"'{cmd}' not found. {installHint}"

/-- Escape a string for safe interpolation inside a POSIX single-quoted shell argument. -/
private def shellQuote (s : String) : String :=
  "'" ++ s.replace "'" "'\\''" ++ "'"

/-- Extract the samply server token from its log output.
    Samply prints a URL like `http://127.0.0.1:{port}/{token}/...` (percent-encoded).
    We decode the URL, split on the known server prefix, and take the first path segment. -/
private def extractToken (output : String) (port : Nat) : Option String := do
  let decoded := System.Uri.unescapeUri output
  let serverUrl := s!"http://127.0.0.1:{port}/"
  let pos ← decoded.find? serverUrl
  let suffix ← (decoded.sliceFrom pos).dropPrefix? serverUrl
  let token := (suffix.takeWhile Char.isAlphanum).toString
  guard !token.isEmpty
  return token

/-- Wait for samply server to be ready by polling the stderr log file.
    Returns the token extracted from the server URL. -/
private def waitForServer (logFile : String) (proc : IO.Process.Child cfg)
    (port : Nat) (timeoutMs : Nat := 30000) : IO String := do
  let startTime ← IO.monoMsNow
  repeat
    if (← IO.monoMsNow) - startTime > timeoutMs then
      throw <| IO.userError "timeout waiting for samply server to start"
    if let some exitCode ← proc.tryWait then
      throw <| IO.userError s!"samply exited with code {exitCode}:\n{← IO.FS.readFile logFile}"
    if let some token := extractToken (← IO.FS.readFile logFile) port then
      return token
    IO.sleep 200

/-- One stack per thread, with a parallel array mapping each requested frame to its function. -/
private def buildSymbolicationRequest (profile : Json)
    : IO (Json × Array (Array Nat)) := do
  let libs ← IO.ofExcept <| profile.getObjValAs? (Array Json) "libs"
  let memoryMap ← libs.mapM fun lib => do
    let debugName ← IO.ofExcept <| lib.getObjValAs? String "debugName"
    let breakpadId ← IO.ofExcept <| lib.getObjValAs? String "breakpadId"
    return toJson #[debugName, breakpadId]
  let threads ← IO.ofExcept <| profile.getObjValAs? (Array Json) "threads"
  let mut stacks := #[]
  let mut funcMaps := #[]
  for thread in threads do
    let ft ← IO.ofExcept <| thread.getObjVal? "frameTable"
    let funcT ← IO.ofExcept <| thread.getObjVal? "funcTable"
    let rt ← IO.ofExcept <| thread.getObjVal? "resourceTable"
    let funcs ← IO.ofExcept <| ft.getObjValAs? (Array Nat) "func"
    let addresses ← IO.ofExcept <| ft.getObjValAs? (Array Json) "address"
    let resources ← IO.ofExcept <| funcT.getObjValAs? (Array Json) "resource"
    let libIndices ← IO.ofExcept <| rt.getObjValAs? (Array Json) "lib"
    let mut seen : Std.HashSet Nat := {}
    let mut frames := #[]
    let mut funcMap := #[]
    for funcIdx in funcs, address in addresses do
      if seen.contains funcIdx then continue
      -- Negative indices and addresses denote labels or frames without native code.
      let some (libIdx, address) := (do
        let address ← address.getNat?.toOption
        let resIdx ← resources[funcIdx]? >>= (·.getNat?.toOption)
        let libIdx ← libIndices[resIdx]? >>= (·.getNat?.toOption)
        guard (libIdx < libs.size)
        return (libIdx, address) : Option (Nat × Nat)) | continue
      seen := seen.insert funcIdx
      frames := frames.push (toJson #[libIdx, address])
      funcMap := funcMap.push funcIdx
    stacks := stacks.push (Json.arr frames)
    funcMaps := funcMaps.push funcMap
  return (Json.mkObj [("memoryMap", Json.arr memoryMap), ("stacks", Json.arr stacks)], funcMaps)

/-- Update each thread's function names, leaving shared strings (e.g. marker labels) intact. -/
private def applySymbols (profile response : Json)
    (funcMaps : Array (Array Nat)) : IO Json := do
  let results ← IO.ofExcept <| response.getObjValAs? (Array Json) "results"
  let some result := results[0]? | throw <| IO.userError "symbolication returned no results"
  let stacks ← IO.ofExcept <| result.getObjValAs? (Array (Array Json)) "stacks"
  let threads ← IO.ofExcept <| profile.getObjValAs? (Array Json) "threads"
  unless stacks.size == threads.size && funcMaps.size == threads.size do
    throw <| IO.userError "symbolication returned the wrong number of stacks"
  let threads ← threads.mapIdxM fun i thread => do
    let frames := stacks[i]!
    let funcMap := funcMaps[i]!
    unless frames.size == funcMap.size do
      throw <| IO.userError "symbolication returned the wrong number of frames"
    let funcT ← IO.ofExcept <| thread.getObjVal? "funcTable"
    let mut names ← IO.ofExcept <| funcT.getObjValAs? (Array Nat) "name"
    let mut strings ← IO.ofExcept <| thread.getObjValAs? (Array String) "stringArray"
    for funcIdx in funcMap, frame in frames do
      let some name := (frame.getStr? <|> frame.getObjValAs? String "function").toOption
        | continue
      if h : funcIdx < names.size then
        let name := Lean.Name.Demangle.demangleSymbol name |>.getD name
        names := names.set funcIdx strings.size
        strings := strings.push name
    return thread.setObjVal! "funcTable" (funcT.setObjVal! "name" (toJson names))
      |>.setObjVal! "stringArray" (toJson strings)
  -- Firefox Profiler otherwise tries to symbolicate again, overwriting demangled names.
  let metadata ← IO.ofExcept <| profile.getObjVal? "meta"
  return profile.setObjVal! "threads" (Json.arr threads)
    |>.setObjVal! "meta" (metadata.setObjVal! "symbolicated" (Json.bool true))

/-- Kill a child process, ignoring errors (e.g. if it already exited). -/
private def killSafe {cfg : IO.Process.StdioConfig} (proc : IO.Process.Child cfg) : IO Unit :=
  try proc.kill; let _ ← proc.wait catch _ => pure ()

/-- Split a pass-through arg list on the first `--`.
    Returns `(samplyArgs, progArgs)`; if there is no `--`, all args are samply args. -/
private def splitOnDash (args : Array String) : Array String × Array String :=
  match args.findIdx? (· == "--") with
  | some i => (args.take i, args.extract (i + 1) args.size)
  | none   => (args, #[])

/-- Run the full profiling pipeline.
    `passthrough` is forwarded verbatim to `samply record`; an inner `--` separates
    samply's own flags from the profiled executable's arguments.
    Returns the path to the output file. -/
public def run (binary : String) (passthrough : Array String)
    (outputPath : Option String := none)
    (port : Nat := 3756) (raw : Bool := false)
    (serve : Bool := true)
    (env : Array (String × Option String) := #[]) : IO String := do
  requireCmd "samply" "Install with: cargo install samply"
  requireCmd "gzip" "gzip is required for profile compression"
  unless raw do requireCmd "curl" "curl is required for symbolication"

  IO.FS.withTempDir fun tmpDir => do
    let rawProfile := (tmpDir / "profile.json.gz").toString
    let out := outputPath.getD (if raw then "profile-raw.json.gz" else "profile-demangled.json.gz")
    let (samplyArgs, progArgs) := splitOnDash passthrough
    IO.eprintln "Recording profile..."
    let recorder ← IO.Process.spawn {
      cmd := "samply", env
      args := #["record", "--save-only", "-o", rawProfile] ++ samplyArgs
              ++ #["--", binary] ++ progArgs
    }
    let exitCode ← recorder.wait
    if exitCode != 0 then
      throw <| IO.userError s!"samply record failed (exit {exitCode})"

    if raw then
      copyFile rawProfile out
      IO.eprintln s!"Raw profile: {out}"
      return out

    IO.eprintln "Starting symbolication server..."
    let samplyLog := (tmpDir / "samply.log").toString
    IO.FS.writeFile samplyLog ""
    -- `exec` ensures cleanup kills samply itself, rather than just its shell.
    let samplyProc ← IO.Process.spawn {
      cmd := "sh"
      args := #["-c",
        s!"exec samply load --no-open -P {port} {shellQuote rawProfile} \
          >{shellQuote samplyLog} 2>&1"]
      stdout := .null
      stderr := .null
      stdin := .null
    }
    try
      let token ← waitForServer samplyLog samplyProc port
      let serverUrl := s!"http://127.0.0.1:{port}/{token}"
      IO.eprintln "Symbolicating and demangling..."
      let rawJson ← IO.Process.run { cmd := "gzip", args := #["-dc", rawProfile] }
      let profile ← IO.ofExcept <| Json.parse rawJson
      let (symbReq, funcMaps) ← buildSymbolicationRequest profile
      let symbResp ← IO.Process.run {
        cmd := "curl"
        args := #["--fail", "-sS", "--noproxy", "*", s!"{serverUrl}/symbolicate/v5",
                  "-H", "Content-Type: application/json", "--data-binary", "@-"]
      } (some symbReq.compress)
      let result ← applySymbols profile (← IO.ofExcept <| Json.parse symbResp) funcMaps
      let tmpJson := tmpDir / "demangled.json"
      IO.FS.writeFile tmpJson result.compress
      discard <| IO.Process.run { cmd := "gzip", args := #[tmpJson.toString] }
      -- Samply opens the file afresh for each request, so its existing server can serve the result.
      IO.FS.rename (tmpDir / "demangled.json.gz") rawProfile
      copyFile rawProfile out
      IO.eprintln s!"Wrote demangled profile: {out}"

      if serve then
        IO.eprintln s!"Serving on {serverUrl}/"
        IO.eprintln "\nOpen in Firefox Profiler:"
        IO.eprintln s!"  https://profiler.firefox.com/from-url/{uriEncode s!"{serverUrl}/profile.json"}"
        IO.eprintln "\nPress Ctrl+C to stop."
        let exitCode ← samplyProc.wait
        if exitCode != 0 then
          throw <| IO.userError s!"samply server exited with code {exitCode}"
      return out
    finally
      killSafe samplyProc

end Lake.Samply
