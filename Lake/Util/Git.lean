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

/--
Try to turn a remote URL into a URL that can be used to e.g.,
make GitHub  API requests. That is, do not accept SSH URLS and
drop an ending `.git`.
-/
def filterUrl? (url : String) : Option String :=
  if url.startsWith "git" then
    none
  else if url.endsWith ".git" then
    some <| url.dropRight 4
  else
    some url

def isFullObjectName (rev : String) : Bool :=
  rev.length == 40 && rev.all fun c => c.isDigit || ('a' <= c && c <= 'f')

def capture (args : Array String) (wd : Option FilePath := none) : LogIO String := do
  let out ← IO.Process.output {cmd := "git", args, cwd := wd}
  if out.exitCode != 0 then
    let mut log := s!"\n> git {" ".intercalate args.toList}\n"
    unless out.stdout.isEmpty do
      log := log ++ s!"stdout:\n{out.stdout.trim}\n"
    unless out.stderr.isEmpty do
      log := log ++ s!"stderr:\n{out.stderr.trim}\n"
    logError log.trim
    error <| "git exited with code " ++ toString out.exitCode
  return out.stdout.trim -- remove, e.g., newline at end

def capture? (args : Array String) (wd : Option FilePath := none) : BaseIO (Option String) := do
  EIO.catchExceptions (h := fun _ => pure none) do
    let out ← IO.Process.output {cmd := "git", args, cwd := wd}
    if out.exitCode = 0 then
      return some out.stdout.trim -- remove, e.g., newline at end
    else
      return none

def exec (args : Array String) (wd : Option FilePath := none) : LogIO PUnit := do
  discard <| capture args wd

def test (args : Array String) (wd : Option FilePath := none) : BaseIO Bool :=
  EIO.catchExceptions (h := fun _ => pure false) do
    let child ← IO.Process.spawn {
      cmd := "git", args, cwd := wd,
      stdout := IO.Process.Stdio.null, stderr := IO.Process.Stdio.null
    }
    return (← child.wait) == 0

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

def captureGit? (args : Array String) (repo : GitRepo) : BaseIO (Option String) :=
  Git.capture? args repo.dir

def execGit (args : Array String) (repo : GitRepo) : LogIO PUnit :=
  Git.exec args repo.dir

def testGit (args : Array String) (repo : GitRepo) : BaseIO Bool :=
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

def resolveRevision? (rev : String) (repo : GitRepo) : BaseIO (Option String) := do
  repo.captureGit? #["rev-parse", "--verify", rev]

def resolveRevision (rev : String) (repo : GitRepo) : LogIO String := do
  repo.captureGit #["rev-parse", "--verify", rev]

def headRevision (repo : GitRepo) : LogIO String :=
  repo.resolveRevision "HEAD"

def resolveRemoteRevision (rev : String) (remote := Git.defaultRemote) (repo : GitRepo) : LogIO String := do
  if Git.isFullObjectName rev then return rev
  if let some rev ← repo.resolveRevision? s!"{remote}/{rev}"  then return rev
  if let some rev ← repo.resolveRevision? rev then return rev
  error s!"cannot find revision {rev} in repository {repo}"

def findRemoteRevision (repo : GitRepo) (rev? : Option String := none) (remote := Git.defaultRemote) : LogIO String := do
  repo.fetch remote; repo.resolveRemoteRevision (rev?.getD Git.upstreamBranch) remote

def branchExists (rev : String) (repo : GitRepo) : BaseIO Bool := do
  repo.testGit #["show-ref", "--verify", s!"refs/heads/{rev}"]

def revisionExists (rev : String) (repo : GitRepo) : BaseIO Bool := do
  repo.testGit #["rev-parse", "--verify", rev ++ "^{commit}"]

def findTag? (rev : String := "HEAD") (repo : GitRepo) : BaseIO (Option String) := do
  repo.captureGit? #["describe", "--tags", "--exact-match", rev]

def getRemoteUrl? (remote := Git.defaultRemote) (repo : GitRepo) : BaseIO (Option String) := do
  repo.captureGit? #["remote", "get-url", remote]

def getFilteredRemoteUrl? (remote := Git.defaultRemote) (repo : GitRepo) : BaseIO (Option String) := OptionT.run do
  Git.filterUrl? (← repo.getRemoteUrl? remote)
