/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

prelude
import Lean.Data.Json
import Lean.Compiler.NameDemangling
public import Lake.Util.Proc
import Lake.Util.IO
import Lake.CLI.Error
import Init.Data.String.Extra
import Init.Data.String.Search
import Init.Data.String.TakeDrop
import Init.While

/-!
# `lake profile`

Profile a Lean executable with [samply](https://github.com/mstange/samply)
and demangle Lean names for [Firefox Profiler](https://profiler.firefox.com).
-/

namespace Lake.Profile

open Lean (Json JsonNumber)

/-- Check that a command is available on PATH. -/
private def requireCmd (cmd : String) (installHint : String) : IO Unit := do
  let result ← IO.Process.output { cmd := "sh", args := #["-c", s!"command -v {cmd}"] }
  if result.exitCode != 0 then
    throw <| IO.userError s!"'{cmd}' not found. {installHint}"

/-- Extract the samply server token from its output.
    Samply prints a URL containing `%2F<TOKEN>%2F` (URL-encoded).
    The token is a 30+ char lowercase alphanumeric string.
    We treat `%` as a non-alphanumeric break, then skip the 2-char hex code
    that follows it when starting the next token. -/
private def extractToken (output : String) : Option String := Id.run do
  let chars := output.toList
  let mut best : String := ""
  let mut current : String := ""
  let mut skipCount : Nat := 0
  for c in chars do
    if skipCount > 0 then
      skipCount := skipCount - 1
    else if c == '%' then
      -- URL-encoded char: treat as break and skip 2 hex digits
      if current.length >= 30 && current.length > best.length then
        best := current
      current := ""
      skipCount := 2
    else if c.isAlphanum then
      current := current.push c
    else
      if current.length >= 30 && current.length > best.length then
        best := current
      current := ""
  if current.length >= 30 && current.length > best.length then
    best := current
  if best.isEmpty then none else some best

/-- Wait for samply server to be ready by polling the stderr log file.
    Returns the token extracted from the server URL. -/
private def waitForServer (logFile : String) (timeoutMs : Nat := 30000) : IO String := do
  let startTime ← IO.monoMsNow
  let mut found := false
  let mut contents := ""
  while !found do
    let now ← IO.monoMsNow
    if now - startTime > timeoutMs then
      throw <| IO.userError "timeout waiting for samply server to start"
    IO.sleep 200
    contents ← IO.FS.readFile logFile
    if contents.contains "profiler.firefox.com" then
      found := true
  match extractToken contents with
  | some token => return token
  | none => throw <| IO.userError "could not extract samply server token"

/-- Build the symbolication request JSON from a raw profile.
    Returns (request JSON, function map for applying results).
    The function map entries are (threadIdx, funcIdx, resultFrameIdx). -/
private def buildSymbolicationRequest (profile : Json)
    : IO (Json × Array (Nat × Nat × Nat)) := do
  let libs ← IO.ofExcept <| profile.getObjValAs? (Array Json) "libs"
  let memoryMap ← libs.mapM fun lib => do
    let debugName ← IO.ofExcept <| lib.getObjValAs? String "debugName"
    let breakpadId ← IO.ofExcept <| lib.getObjValAs? String "breakpadId"
    return Json.arr #[Json.str debugName, Json.str breakpadId]
  let threads ← IO.ofExcept <| profile.getObjValAs? (Array Json) "threads"
  let mut frames : Array Json := #[]
  let mut funcMap : Array (Nat × Nat × Nat) := #[]
  for hi : threadIdx in [:threads.size] do
    let thread := threads[threadIdx]
    let some ft := (thread.getObjValAs? Json "frameTable").toOption | continue
    let some funcT := (thread.getObjValAs? Json "funcTable").toOption | continue
    let some rt := (thread.getObjValAs? Json "resourceTable").toOption | continue
    let some ftFunc := (ft.getObjValAs? (Array Json) "func").toOption | continue
    let some ftAddr := (ft.getObjValAs? (Array Json) "address").toOption | continue
    let some ftLen := (ft.getObjValAs? Nat "length").toOption | continue
    let some funcRes := (funcT.getObjValAs? (Array Json) "resource").toOption | continue
    let some rtLib := (rt.getObjValAs? (Array Json) "lib").toOption | continue
    let mut seen : Std.HashSet Nat := {}
    for i in [:ftLen] do
      if h1 : i < ftFunc.size then
        if h2 : i < ftAddr.size then
          if let some funcIdx := ftFunc[i].getNat?.toOption then
            if !seen.contains funcIdx then
              seen := seen.insert funcIdx
              if hf : funcIdx < funcRes.size then
                if let some resIdx := funcRes[funcIdx].getNat?.toOption then
                  if hr : resIdx < rtLib.size then
                    if let some libIdx := rtLib[resIdx].getNat?.toOption then
                      frames := frames.push <|
                        Json.arr #[Json.num (JsonNumber.fromNat libIdx), ftAddr[i]]
                      funcMap := funcMap.push (threadIdx, funcIdx, frames.size - 1)
  let req := Json.mkObj [
    ("memoryMap", Json.arr memoryMap),
    ("stacks", Json.arr #[Json.arr frames])
  ]
  return (req, funcMap)

/-- Parse symbolication response and apply demangled names to the profile. -/
private def applySymbols (profile : Json) (response : Json)
    (funcMap : Array (Nat × Nat × Nat)) : IO Json := do
  let results ← IO.ofExcept <| response.getObjValAs? (Array Json) "results"
  if h : 0 < results.size then
    let stacks ← IO.ofExcept <| results[0].getObjValAs? (Array Json) "stacks"
    if hs : 0 < stacks.size then
      let frameResults ← IO.ofExcept <| stacks[0].getArr?
      -- Extract symbol names from response
      let symbols : Array (Option String) := frameResults.map fun entry =>
        match entry with
        | Json.str s => some s
        | _ => (entry.getObjValAs? String "function").toOption
      -- Apply demangled names to profile
      let mut threads ← IO.ofExcept <| profile.getObjValAs? (Array Json) "threads"
      for (threadIdx, funcIdx, resultIdx) in funcMap do
        if hr : resultIdx < symbols.size then
          if let some symbolName := symbols[resultIdx] then
            let demangled := Lean.Name.Demangle.demangleSymbol symbolName |>.getD symbolName
            if ht : threadIdx < threads.size then
              let thread := threads[threadIdx]
              if let some funcT := (thread.getObjValAs? Json "funcTable").toOption then
                if let some nameArr := (funcT.getObjValAs? (Array Json) "name").toOption then
                  if hf : funcIdx < nameArr.size then
                    if let some nameIdx := nameArr[funcIdx].getNat?.toOption then
                      if let some sa := (thread.getObjValAs? (Array Json) "stringArray").toOption then
                        if hn : nameIdx < sa.size then
                          let sa' := sa.set nameIdx (Json.str demangled)
                          let thread' := thread.setObjVal! "stringArray" (Json.arr sa')
                          threads := threads.set threadIdx thread'
      return profile.setObjVal! "threads" (Json.arr threads)
  return profile

/-- Run the full profiling pipeline.
    Returns the path to the output file. -/
public def run (binary : String) (args : Array String)
    (outputPath : Option String := none)
    (rate : Nat := 1000) (port : Nat := 3756) (raw : Bool := false) : IO String := do
  requireCmd "samply" "Install with: cargo install samply"
  requireCmd "gzip" "gzip is required for profile compression"

  let tmpResult ← IO.Process.output {
    cmd := "mktemp", args := #["-d", "/tmp/lake-profile-XXXXXX"]
  }
  if tmpResult.exitCode != 0 then throw <| IO.userError "failed to create temp directory"
  let tmpDir := tmpResult.stdout.trimAscii.toString
  let rawProfile := s!"{tmpDir}/profile.json.gz"
  let defaultOut := s!"{tmpDir}/profile-demangled.json.gz"

  -- Record
  IO.eprintln s!"Recording profile (rate={rate} Hz)..."
  let recordResult ← IO.Process.output {
    cmd := "samply"
    args := #["record", "--save-only", "-o", rawProfile,
              "-r", toString rate, binary] ++ args
  }
  if recordResult.exitCode != 0 then
    IO.eprintln recordResult.stderr
    throw <| IO.userError s!"samply record failed (exit {recordResult.exitCode})"

  if raw then
    let out := outputPath.getD rawProfile
    if out != rawProfile then
      let _ ← IO.Process.output { cmd := "cp", args := #[rawProfile, out] }
    IO.eprintln s!"Raw profile: {out}"
    return out

  -- Start symbolication server
  -- Use `exec` so killing the shell process also kills samply.
  IO.eprintln "Starting symbolication server..."
  let samplyLog := s!"{tmpDir}/samply.log"
  IO.FS.writeFile samplyLog ""
  let samplyProc ← IO.Process.spawn {
    cmd := "sh"
    args := #["-c", s!"exec samply load --no-open -P {port} '{rawProfile}' >'{samplyLog}' 2>&1"]
    stdout := .null
    stderr := .null
    stdin := .null
  }
  let token ← waitForServer samplyLog
  let serverUrl := s!"http://127.0.0.1:{port}/{token}"

  -- Read raw profile by decompressing to temp file
  IO.eprintln "Symbolicating and demangling..."
  let rawJson := s!"{tmpDir}/raw.json"
  let gunzip ← IO.Process.output {
    cmd := "sh", args := #["-c", s!"zcat '{rawProfile}' > '{rawJson}'"]
  }
  if gunzip.exitCode != 0 then
    samplyProc.kill; throw <| IO.userError "failed to decompress profile"
  let rawJsonStr ← IO.FS.readFile rawJson
  let profile ← IO.ofExcept <| Json.parse rawJsonStr

  -- Build and send symbolication request
  let (symbReq, funcMap) ← buildSymbolicationRequest profile
  let symbUrl := s!"{serverUrl}/symbolicate/v5"
  let curl ← IO.Process.output {
    cmd := "curl"
    args := #["-s", "-X", "POST", symbUrl,
              "-H", "Content-Type: application/json",
              "-d", symbReq.compress]
  }
  if curl.exitCode != 0 then
    samplyProc.kill; throw <| IO.userError "symbolication request failed"
  if curl.stdout.isEmpty then
    samplyProc.kill; throw <| IO.userError "symbolication returned empty response"
  let symbResp ← IO.ofExcept <| Json.parse curl.stdout

  -- Apply demangled names
  let result ← applySymbols profile symbResp funcMap

  -- Kill symbolication server
  samplyProc.kill

  -- Write compressed output
  let out := outputPath.getD defaultOut
  let jsonStr := result.compress
  let tmpJson := s!"{tmpDir}/demangled.json"
  IO.FS.writeFile tmpJson jsonStr
  let gzResult ← IO.Process.output {
    cmd := "sh", args := #["-c", s!"gzip -c '{tmpJson}' > '{out}'"]
  }
  if gzResult.exitCode != 0 then throw <| IO.userError "gzip failed"

  let count := funcMap.size
  IO.eprintln s!"Demangled {count} names, wrote {out}"

  -- Serve the demangled profile using samply's HTTP server (which handles CORS,
  -- works with VSCode port forwarding, etc). We construct the Firefox Profiler URL
  -- ourselves, omitting `?symbolServer=` so it doesn't re-symbolicate with mangled names.
  -- TODO: replace samply server with `Std.Http.Server` once #12151 lands.
  let servePort := port + 1
  let samplyServeLog := s!"{tmpDir}/samply-serve.log"
  IO.FS.writeFile samplyServeLog ""
  let serveProc ← IO.Process.spawn {
    cmd := "sh"
    args := #["-c", s!"exec samply load --no-open -P {servePort} '{out}' >'{samplyServeLog}' 2>&1"]
    stdout := .null
    stderr := .null
    stdin := .null
  }
  let serveToken ← waitForServer samplyServeLog
  let profileUrl := s!"http%3A%2F%2F127.0.0.1%3A{servePort}%2F{serveToken}%2Fprofile.json"
  -- Print the server URL so VSCode detects and auto-forwards the port.
  IO.eprintln s!"Serving on http://127.0.0.1:{servePort}/"
  IO.eprintln s!"\nOpen in Firefox Profiler:"
  IO.eprintln s!"  https://profiler.firefox.com/from-url/{profileUrl}"
  IO.eprintln s!"\nPress Ctrl+C to stop."
  let _ ← serveProc.wait
  return out

end Lake.Profile
