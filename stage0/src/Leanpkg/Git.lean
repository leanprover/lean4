/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner, Sebastian Ullrich
-/
import Leanpkg.LeanVersion

namespace Leanpkg

def upstreamGitBranch :=
  if Lean.version.isRelease then
    "Lean-" ++ leanVersionStringCore
  else
    "master"

def gitdefaultRevision : Option String → String
  | none => upstreamGitBranch
  | some branch => branch

def gitParseRevision (gitRepoDir : String) (rev : String) : IO String := do
  let rev ← IO.Process.run {cmd := "git", args := #["rev-parse", "-q", "--verify", rev], cwd := gitRepoDir}
  rev.trim -- remove newline at end

def gitHeadRevision (gitRepoDir : String) : IO String :=
  gitParseRevision gitRepoDir "HEAD"

def gitParseOriginRevision (gitRepoDir : String) (rev : String) : IO String :=
  (gitParseRevision gitRepoDir $ "origin/" ++ rev) <|> gitParseRevision gitRepoDir rev
    <|> throw (IO.userError s!"cannot find revision {rev} in repository {gitRepoDir}")

def gitLatestOriginRevision (gitRepoDir : String) (branch : Option String) : IO String := do
  discard <| IO.Process.run {cmd := "git", args := #["fetch"], cwd := gitRepoDir}
  gitParseOriginRevision gitRepoDir (gitdefaultRevision branch)

def gitRevisionExists (gitRepoDir : String) (rev : String) : IO Bool := do
  try
    discard <| gitParseRevision gitRepoDir (rev ++ "^{commit}")
    true
  catch _ => false

end Leanpkg
