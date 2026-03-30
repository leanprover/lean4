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
import Init.System.Uri
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

/-- Escape a string for safe interpolation inside a POSIX single-quoted shell argument. -/
private def shellQuote (s : String) : String :=
  "'" ++ s.replace "'" "'\\''" ++ "'"

/-- Percent-encode a string for use as a URL path component (RFC 3986).
    Only unreserved characters (A-Z, a-z, 0-9, `-`, `.`, `_`, `~`) are left unencoded.
    We can't use `System.Uri.escapeUri` here because it doesn't encode `/`,
    which must be encoded for the Firefox Profiler `from-url/` route
    (it splits on `/` to extract the embedded URL as a single path segment). -/
private def percentEncode (s : String) : String := Id.run do
  let hexDigit (n : UInt8) : Char :=
    if n < 10 then Char.ofNat (n.toNat + '0'.toNat)
    else Char.ofNat (n.toNat - 10 + 'A'.toNat)
  let mut acc : String := ""
  for b in s.toUTF8 do
    if (b >= 0x41 && b <= 0x5A)     -- A-Z
      || (b >= 0x61 && b <= 0x7A)   -- a-z
      || (b >= 0x30 && b <= 0x39)   -- 0-9
      || b == 0x2D || b == 0x2E || b == 0x5F || b == 0x7E  -- - . _ ~
    then
      acc := acc.push (Char.ofNat b.toNat)
    else
      acc := (acc.push '%').push (hexDigit (b / 16)) |>.push (hexDigit (b % 16))
  return acc

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
  let mut found := false
  let mut contents := ""
  while !found do
    let now ← IO.monoMsNow
    if now - startTime > timeoutMs then
      throw <| IO.userError "timeout waiting for samply server to start"
    if let some exitCode ← proc.tryWait then
      contents ← IO.FS.readFile logFile
      throw <| IO.userError s!"samply exited with code {exitCode}:\n{contents}"
    IO.sleep 200
    contents ← IO.FS.readFile logFile
    if contents.contains "profiler.firefox.com" then
      found := true
  match extractToken contents port with
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

/-- Kill a child process, ignoring errors (e.g. if it already exited). -/
private def killSafe {cfg : IO.Process.StdioConfig} (proc : IO.Process.Child cfg) : IO Unit :=
  try proc.kill; let _ ← proc.wait catch _ => pure ()

/-- Run the full profiling pipeline.
    Returns the path to the output file. -/
public def run (binary : String) (args : Array String)
    (outputPath : Option String := none)
    (rate : Nat := 1000) (port : Nat := 3756) (raw : Bool := false)
    (serve : Bool := true) : IO String := do
  requireCmd "samply" "Install with: cargo install samply"
  requireCmd "gzip" "gzip is required for profile compression"

  let tmpResult ← IO.Process.output {
    cmd := "mktemp", args := #["-d", "/tmp/lake-profile-XXXXXX"]
  }
  if tmpResult.exitCode != 0 then throw <| IO.userError "failed to create temp directory"
  let tmpDir := tmpResult.stdout.trimAscii.toString
  let rawProfile := s!"{tmpDir}/profile.json.gz"
  let defaultOut := "profile-demangled.json.gz"

  try
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
      let out := outputPath.getD "profile-raw.json.gz"
      let cpResult ← IO.Process.output { cmd := "cp", args := #[rawProfile, out] }
      if cpResult.exitCode != 0 then
        throw <| IO.userError s!"failed to copy profile to {out}"
      IO.eprintln s!"Raw profile: {out}"
      return out

    -- Start symbolication server
    -- Use `exec` so killing the shell process also kills samply.
    IO.eprintln "Starting symbolication server..."
    let samplyLog := s!"{tmpDir}/samply.log"
    IO.FS.writeFile samplyLog ""
    let out := outputPath.getD defaultOut
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

      -- Read raw profile by decompressing to temp file
      IO.eprintln "Symbolicating and demangling..."
      let rawJson := s!"{tmpDir}/raw.json"
      let gunzip ← IO.Process.output {
        cmd := "sh"
        args := #["-c",
          s!"zcat {shellQuote rawProfile} > {shellQuote rawJson}"]
      }
      if gunzip.exitCode != 0 then
        throw <| IO.userError "failed to decompress profile"
      let rawJsonStr ← IO.FS.readFile rawJson
      let profile ← IO.ofExcept <| Json.parse rawJsonStr

      -- Build and send symbolication request
      let (symbReq, funcMap) ← buildSymbolicationRequest profile
      let symbUrl := s!"{serverUrl}/symbolicate/v5"
      let curl ← IO.Process.output {
        cmd := "curl"
        args := #["-sS", "-X", "POST", symbUrl,
                  "-H", "Content-Type: application/json",
                  "-d", symbReq.compress]
      }
      if curl.exitCode != 0 then
        throw <| IO.userError s!"symbolication request failed: {curl.stderr}"
      if curl.stdout.isEmpty then
        throw <| IO.userError "symbolication returned empty response"
      let symbResp ← IO.ofExcept <| Json.parse curl.stdout

      -- Apply demangled names and write compressed output
      let result ← applySymbols profile symbResp funcMap
      let jsonStr := result.compress
      let tmpJson := s!"{tmpDir}/demangled.json"
      IO.FS.writeFile tmpJson jsonStr
      let gzResult ← IO.Process.output { cmd := "gzip", args := #[tmpJson] }
      if gzResult.exitCode != 0 then throw <| IO.userError "gzip failed"
      let mvResult ← IO.Process.output { cmd := "mv", args := #[s!"{tmpJson}.gz", out] }
      if mvResult.exitCode != 0 then
        throw <| IO.userError s!"failed to write output to {out}"

      IO.eprintln s!"Demangled {funcMap.size} names, wrote {out}"
    finally
      killSafe samplyProc

    unless serve do return out

    -- Serve the demangled profile using samply's HTTP server (which handles CORS,
    -- works with VSCode port forwarding, etc). We construct the Firefox Profiler URL
    -- ourselves, omitting `?symbolServer=` so it doesn't re-symbolicate with mangled names.
    -- TODO: replace samply server with `Std.Http.Server` once #12151 lands.
    let servePort := port + 1
    let samplyServeLog := s!"{tmpDir}/samply-serve.log"
    IO.FS.writeFile samplyServeLog ""
    let serveProc ← IO.Process.spawn {
      cmd := "sh"
      args := #["-c",
        s!"exec samply load --no-open -P {servePort} {shellQuote out} \
          >{shellQuote samplyServeLog} 2>&1"]
      stdout := .null
      stderr := .null
      stdin := .null
    }
    try
      let serveToken ← waitForServer samplyServeLog serveProc servePort
      let profileUrl :=
        percentEncode s!"http://127.0.0.1:{servePort}/{serveToken}/profile.json"
      -- Print the server URL so VSCode detects and auto-forwards the port.
      IO.eprintln s!"Serving on http://127.0.0.1:{servePort}/"
      IO.eprintln s!"\nOpen in Firefox Profiler:"
      IO.eprintln s!"  https://profiler.firefox.com/from-url/{profileUrl}"
      IO.eprintln s!"\nPress Ctrl+C to stop."
      let _ ← serveProc.wait
    finally
      killSafe serveProc
    return out
  finally
    removeDirAllIfExists tmpDir

end Lake.Profile
