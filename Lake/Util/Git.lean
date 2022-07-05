/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner, Sebastian Ullrich, Mac Malone
-/
import Lake.Util.Log
import Lake.Util.Lift

open System
namespace Lake

namespace Git

def defaultRemote :=
  "origin"

def upstreamBranch :=
  "master"

def isFullObjectName (rev : String) : Bool :=
  rev.length == 40 && rev.all fun c => c.isDigit || ('a' <= c && c <= 'f')

def capture (args : Array String) (wd : Option FilePath := none) : LogIO String := do
  let out ← IO.Process.output {cmd := "git", args, cwd := wd}
  if out.exitCode != 0 then
    let mut log := ""
    unless out.stdout.isEmpty do
      log := log ++ s!"stdout:\n{out.stdout.trim}\n"
    unless out.stderr.isEmpty do
      log := log ++ s!"stderr:\n{out.stderr.trim}\n"
    logError log.trim
    error <| "git exited with code " ++ toString out.exitCode
  return out.stdout

def exec (args : Array String) (wd : Option FilePath := none) : LogIO PUnit := do
  discard <| capture args wd

def test (args : Array String) (wd : Option FilePath := none) : LogT BaseIO Bool :=
  let act : IO _ := do
    let child ← IO.Process.spawn {
      cmd := "git", args, cwd := wd,
      stdout := IO.Process.Stdio.null, stderr := IO.Process.Stdio.null
    }
    return (← child.wait) == 0
  act.catchExceptions fun _ => pure false

end Git

structure GitRepo where
  dir : FilePath

instance : ToString GitRepo := ⟨(·.dir.toString)⟩

namespace GitRepo

def cwd : GitRepo := ⟨"."⟩

def dirExists (repo : GitRepo) : BaseIO Bool :=
  repo.dir.isDir

def captureGit (args : Array String) (repo : GitRepo) : LogIO String :=
  Git.capture args repo.dir

def execGit (args : Array String) (repo : GitRepo) : LogIO PUnit :=
  Git.exec args repo.dir

def testGit (args : Array String) (repo : GitRepo) : LogIO Bool :=
  Git.test args repo.dir

def clone (url : String) (repo : GitRepo) : LogIO PUnit  :=
  Git.exec #["clone", url, repo.dir.toString]

def quietInit (repo : GitRepo) : LogIO PUnit  :=
  repo.execGit #["init", "-q"]

def fetch (repo : GitRepo) (remote := Git.defaultRemote) : LogIO PUnit  :=
  repo.execGit #["fetch", remote]

def checkoutBranch (branch : String) (repo : GitRepo) : LogIO PUnit :=
  repo.execGit #["checkout", "-B", branch]

def checkoutDetach (hash : String) (repo : GitRepo) : LogIO PUnit  :=
  repo.execGit #["checkout", "--detach", hash]

def parseRevision (rev : String) (repo : GitRepo) : LogIO String := do
  let rev ← repo.captureGit #["rev-parse", "--verify", rev]
  pure rev.trim -- remove newline at end

def headRevision (repo : GitRepo) : LogIO String :=
  repo.parseRevision "HEAD"

def parseRemoteRevision (rev : String) (remote := Git.defaultRemote) (repo : GitRepo) : LogIO String := do
  if Git.isFullObjectName rev then return rev
  repo.parseRevision (s!"{remote}/{rev}") <|> repo.parseRevision rev
    <|> error s!"cannot find revision {rev} in repository {repo}"

def findRemoteRevision (repo : GitRepo) (rev? : Option String := none)  (remote := Git.defaultRemote) : LogIO String := do
  repo.fetch remote; repo.parseRemoteRevision (rev?.getD Git.upstreamBranch) remote

def branchExists (rev : String) (repo : GitRepo) : LogIO Bool := do
  repo.testGit #["show-ref", "--verify", s!"refs/heads/{rev}"]

def revisionExists (rev : String) (repo : GitRepo) : LogIO Bool := do
  repo.testGit #["rev-parse", "--verify", rev ++ "^{commit}"]
