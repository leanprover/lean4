-- Copyright (c) 2026 Lean FRO. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Mac Malone, Claude Code

/-!
A `curl` that misreports its transfers, covering failures that no server
response can produce. `BAD_CURL` selects the misreport, and the real `curl`
at `REAL_CURL` performs whatever transfer still has to happen:

* `quiet`: report no transfer at all, and exit successfully
* `exitcode`: report every transfer as failed, leaving each output file
  complete and correct
* `nofile`: report every transfer as successful, having deleted the files it
  wrote from `BAD_CURL_DIR`
-/

def getEnv (name : String) : IO String := do
  let some value ← IO.getEnv name
    | throw (IO.userError s!"{name} must be set")
  return value

def runCurl (args : List String) : IO IO.Process.Output := do
  IO.Process.output {cmd := ← getEnv "REAL_CURL", args := args.toArray}

def main (args : List String) : IO UInt32 := do
  match ← IO.getEnv "BAD_CURL" with
  | some "exitcode" =>
    let out ← runCurl args
    IO.print out.stdout
    IO.eprint (out.stderr.replace "\"exitcode\":0," "\"exitcode\":18,")
  | some "nofile" =>
    let out ← runCurl args
    -- Deleted before the report is written, so nothing can read them first
    for entry in (← System.FilePath.readDir (← getEnv "BAD_CURL_DIR")) do
      if entry.fileName.endsWith ".tmp" then
        IO.FS.removeFile entry.path
    IO.print out.stdout
    IO.eprint out.stderr
  | _ => pure ()
  return 0
