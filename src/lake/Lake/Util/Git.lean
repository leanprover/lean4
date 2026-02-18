/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner, Sebastian Ullrich, Mac Malone
-/
module

prelude
public import Init.Data.ToString
public import Lake.Util.Proc
import Init.Data.String.TakeDrop
import Init.Data.String.Search

open System
namespace Lake

namespace Git

public def defaultRemote : String :=
  "origin"

public def upstreamBranch : String :=
  "master"

/--
Try to turn a remote URL into a URL that can be used to, e.g.,
make GitHub API requests. That is, do not accept SSH URLs and
drop an ending `.git`.
-/
public def filterUrl? (url : String) : Option String :=
  if url.startsWith "git" then
    none
  else if url.endsWith ".git" then
    some <| url.dropEnd 4 |>.copy
  else
    some url

public def isFullObjectName (rev : String) : Bool :=
  rev.chars.length == 40 && rev.all fun c => c.isDigit || ('a' <= c && c <= 'f')

end Git

public structure GitRepo where
  dir : FilePath

public instance : Coe FilePath GitRepo := ⟨(⟨·⟩)⟩
public instance : ToString GitRepo := ⟨(·.dir.toString)⟩

namespace GitRepo

public def cwd : GitRepo := ⟨"."⟩

@[inline] public def dirExists (repo : GitRepo) : BaseIO Bool :=
  repo.dir.isDir

@[inline] public def captureGit (args : Array String) (repo : GitRepo) : LogIO String :=
  captureProc {cmd := "git", args, cwd := repo.dir}

@[inline] public def captureGit? (args : Array String) (repo : GitRepo) : BaseIO (Option String) :=
  captureProc? {cmd := "git", args, cwd := repo.dir}

@[inline] public def execGit (args : Array String) (repo : GitRepo) : LogIO PUnit :=
  proc {cmd := "git", args, cwd := repo.dir} (quiet := true)

@[inline] public def testGit (args : Array String) (repo : GitRepo) : BaseIO Bool :=
  testProc {cmd := "git", args, cwd := repo.dir}

public def clone (url : String) (repo : GitRepo) : LogIO PUnit  :=
  proc {cmd := "git", args := #["clone", url, repo.dir.toString]} (quiet := true)

public def quietInit (repo : GitRepo) : LogIO PUnit  :=
  repo.execGit #["init", "-q"]

public def insideWorkTree (repo : GitRepo) : BaseIO Bool := do
  repo.testGit #["rev-parse", "--is-inside-work-tree"]

public def fetch (repo : GitRepo) (remote := Git.defaultRemote) : LogIO PUnit  :=
  repo.execGit #["fetch", "--tags", "--force", remote]

public def checkoutBranch (branch : String) (repo : GitRepo) : LogIO PUnit :=
  repo.execGit #["checkout", "-B", branch]

public def checkoutDetach (hash : String) (repo : GitRepo) : LogIO PUnit  :=
  repo.execGit #["checkout", "--detach", hash, "--"]

public def resolveRevision? (rev : String) (repo : GitRepo) : BaseIO (Option String) := do
  repo.captureGit? #["rev-parse", "--verify", "--end-of-options", rev]

public def resolveRevision (rev : String) (repo : GitRepo) : LogIO String := do
  if Git.isFullObjectName rev then return rev
  if let some rev ← repo.resolveRevision? rev then return rev
  error s!"{repo}: revision not found '{rev}'"

@[inline] public def getHeadRevision? (repo : GitRepo) : BaseIO (Option String) :=
  repo.resolveRevision? "HEAD"

public def getHeadRevision (repo : GitRepo) : LogIO String := do
  if let some rev ← repo.getHeadRevision? then return rev
  error s!"{repo}: could not resolve 'HEAD' to a commit; \
    the repository may be corrupt, so you may need to remove it and try again"

public def getHeadRevisions (repo : GitRepo) (n : Nat := 0) : LogIO (Array String) := do
  let args := #["rev-list", "HEAD"]
  let args := if n != 0 then args ++ #["-n", toString n] else args
  let revs ← repo.captureGit args
  return revs.split '\n' |>.toStringArray

public def resolveRemoteRevision (rev : String) (remote := Git.defaultRemote) (repo : GitRepo) : LogIO String := do
  if Git.isFullObjectName rev then return rev
  if let some rev ← repo.resolveRevision? s!"{remote}/{rev}"  then return rev
  if let some rev ← repo.resolveRevision? rev then return rev
  error s!"{repo}: revision not found '{rev}'"

public def findRemoteRevision (repo : GitRepo) (rev? : Option String := none) (remote := Git.defaultRemote) : LogIO String := do
  repo.fetch remote; repo.resolveRemoteRevision (rev?.getD Git.upstreamBranch) remote

public def branchExists (rev : String) (repo : GitRepo) : BaseIO Bool := do
  repo.testGit #["show-ref", "--verify", s!"refs/heads/{rev}"]

public def revisionExists (rev : String) (repo : GitRepo) : BaseIO Bool := do
  repo.testGit #["rev-parse", "--verify", rev ++ "^{commit}"]

public def getTags (repo : GitRepo) : BaseIO (List String) := do
  let some out ← repo.captureGit? #["tag"] | return []
  return out.split '\n' |>.toStringList

public def findTag? (rev : String := "HEAD") (repo : GitRepo) : BaseIO (Option String) := do
  repo.captureGit? #["describe", "--tags", "--exact-match", rev]

public def getRemoteUrl?
  (remote := Git.defaultRemote) (repo : GitRepo)
: BaseIO (Option String) := do repo.captureGit? #["remote", "get-url", remote]

public def getFilteredRemoteUrl?
  (remote := Git.defaultRemote) (repo : GitRepo)
: BaseIO (Option String) := OptionT.run do Git.filterUrl? (← repo.getRemoteUrl? remote)

public def hasNoDiff (repo : GitRepo) : BaseIO Bool := do
  repo.testGit #["diff", "HEAD", "--exit-code"]

@[inline] public def hasDiff (repo : GitRepo) : BaseIO Bool := do
  not <$> repo.hasNoDiff
