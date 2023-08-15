/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner, Sebastian Ullrich, Mac Malone
-/
import Lake.Util.Proc
import Lake.Util.Lift

open System
namespace Lake

namespace Git

@[noinline] def defaultRemote :=
  "origin"

@[noinline] def upstreamBranch :=
  "master"

/--
Try to turn a remote URL into a URL that can be used to, e.g.,
make GitHub API requests. That is, do not accept SSH URLs and
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

end Git

structure GitRepo where
  dir : FilePath

instance : ToString GitRepo := ⟨(·.dir.toString)⟩

namespace GitRepo

@[noinline] def cwd : GitRepo := ⟨"."⟩

@[inline] def dirExists (repo : GitRepo) : BaseIO Bool :=
  repo.dir.isDir

@[inline] def captureGit (args : Array String) (repo : GitRepo) : LogIO String :=
  captureProc {cmd := "git", args, cwd := repo.dir}

@[inline] def captureGit? (args : Array String) (repo : GitRepo) : BaseIO (Option String) :=
  captureProc? {cmd := "git", args, cwd := repo.dir}

@[inline] def execGit (args : Array String) (repo : GitRepo) : LogIO PUnit :=
  proc {cmd := "git", args, cwd := repo.dir} (quiet := true)

@[inline] def testGit (args : Array String) (repo : GitRepo) : BaseIO Bool :=
  testProc {cmd := "git", args, cwd := repo.dir}

@[inline] def clone (url : String) (repo : GitRepo) : LogIO PUnit  :=
  proc {cmd := "git", args := #["clone", url, repo.dir.toString]} (quiet := true)

@[inline] def quietInit (repo : GitRepo) : LogIO PUnit  :=
  repo.execGit #["init", "-q"]

@[inline] def fetch (repo : GitRepo) (remote := Git.defaultRemote) : LogIO PUnit  :=
  repo.execGit #["fetch", remote]

@[inline] def checkoutBranch (branch : String) (repo : GitRepo) : LogIO PUnit :=
  repo.execGit #["checkout", "-B", branch]

@[inline] def checkoutDetach (hash : String) (repo : GitRepo) : LogIO PUnit  :=
  repo.execGit #["checkout", "--detach", hash]

@[inline] def resolveRevision? (rev : String) (repo : GitRepo) : BaseIO (Option String) := do
  repo.captureGit? #["rev-parse", "--verify", rev]

@[inline] def resolveRevision (rev : String) (repo : GitRepo) : LogIO String := do
  repo.captureGit #["rev-parse", "--verify", rev]

@[inline] def getHeadRevision (repo : GitRepo) : LogIO String :=
  repo.resolveRevision "HEAD"

@[inline] def getHeadRevision? (repo : GitRepo) : BaseIO (Option String) :=
  repo.resolveRevision? "HEAD"

def resolveRemoteRevision (rev : String) (remote := Git.defaultRemote) (repo : GitRepo) : LogIO String := do
  if Git.isFullObjectName rev then return rev
  if let some rev ← repo.resolveRevision? s!"{remote}/{rev}"  then return rev
  if let some rev ← repo.resolveRevision? rev then return rev
  error s!"cannot find revision {rev} in repository {repo}"

def findRemoteRevision (repo : GitRepo) (rev? : Option String := none) (remote := Git.defaultRemote) : LogIO String := do
  repo.fetch remote; repo.resolveRemoteRevision (rev?.getD Git.upstreamBranch) remote

@[inline] def branchExists (rev : String) (repo : GitRepo) : BaseIO Bool := do
  repo.testGit #["show-ref", "--verify", s!"refs/heads/{rev}"]

@[inline] def revisionExists (rev : String) (repo : GitRepo) : BaseIO Bool := do
  repo.testGit #["rev-parse", "--verify", rev ++ "^{commit}"]

@[inline] def findTag? (rev : String := "HEAD") (repo : GitRepo) : BaseIO (Option String) := do
  repo.captureGit? #["describe", "--tags", "--exact-match", rev]

@[inline] def getRemoteUrl? (remote := Git.defaultRemote) (repo : GitRepo) : BaseIO (Option String) := do
  repo.captureGit? #["remote", "get-url", remote]

def getFilteredRemoteUrl? (remote := Git.defaultRemote) (repo : GitRepo) : BaseIO (Option String) := OptionT.run do
  Git.filterUrl? (← repo.getRemoteUrl? remote)

@[inline] def hasNoDiff (repo : GitRepo) : BaseIO Bool := do
  repo.testGit #["diff", "--exit-code"]

@[inline] def hasDiff (repo : GitRepo) : BaseIO Bool := do
  not <$> repo.hasNoDiff
