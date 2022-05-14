/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner, Sebastian Ullrich, Mac Malone
-/

open System
namespace Lake.Git

def upstreamBranch :=
  "master"

def isFullObjectName (rev : String) : Bool :=
  rev.length == 40 && rev.all fun c => c.isDigit || ('a' <= c && c <= 'f')

def defaultRevision : Option String → String
  | none => upstreamBranch
  | some branch => branch

def execGit (args : Array String) (repo : Option FilePath := none) : IO PUnit := do
  let child ← IO.Process.spawn {
    cmd := "git", args, cwd := repo,
    stdout := IO.Process.Stdio.null, stderr := IO.Process.Stdio.null
  }
  let exitCode ← child.wait
  if exitCode != 0 then
    throw <| IO.userError <| "git exited with code " ++ toString exitCode

def captureGit (args : Array String) (repo : Option FilePath := none) : IO String := do
  let out ← IO.Process.output {cmd := "git", args, cwd := repo}
  if out.exitCode != 0 then
    throw <| IO.userError <| "git exited with code " ++ toString out.exitCode
  return out.stdout

def clone (url : String) (dir : FilePath) :=
  execGit #["clone", url, dir.toString]

def quietInit (repo : Option FilePath := none) :=
  execGit #["init", "-q"] repo

def fetch (repo : Option FilePath := none) :=
  execGit #["fetch"] repo

def checkoutBranch (branch : String) (repo : Option FilePath := none) :=
  execGit #["checkout", "-B", branch] repo

def checkoutDetach (hash : String) (repo : Option FilePath := none)  :=
  execGit #["checkout", "--detach", hash] repo

def parseRevision (rev : String) (repo : Option FilePath := none) : IO String := do
  let rev ← captureGit #["rev-parse", "-q", "--verify", rev] repo
  pure rev.trim -- remove newline at end

def headRevision (repo : Option FilePath := none) : IO String :=
  parseRevision "HEAD" repo

def parseOriginRevision (rev : String) (repo : Option FilePath := none) : IO String := do
  if isFullObjectName rev then return rev
  (parseRevision ("origin/" ++ rev) repo) <|> parseRevision rev repo
    <|> throw (IO.userError s!"cannot find revision {rev} in repository {repo}")

def latestOriginRevision (branch : Option String) (repo : Option FilePath := none) : IO String := do
  execGit #["fetch"] repo
  parseOriginRevision (defaultRevision branch) repo

def revisionExists (rev : String) (repo : Option FilePath := none) : IO Bool := do
  try
    discard <| parseRevision (rev ++ "^{commit}") repo
    pure true
  catch _ => pure false
