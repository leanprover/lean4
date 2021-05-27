/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner, Sebastian Ullrich
-/
import Leanpkg.LeanVersion

open System

namespace Leanpkg

def upstreamGitBranch :=
  "master"

def gitdefaultRevision : Option String → String
  | none => upstreamGitBranch
  | some branch => branch

def gitParseRevision (gitRepo : FilePath) (rev : String) : IO String := do
  let rev ← IO.Process.run {cmd := "git", args := #["rev-parse", "-q", "--verify", rev], cwd := gitRepo}
  rev.trim -- remove newline at end

def gitHeadRevision (gitRepo : FilePath) : IO String :=
  gitParseRevision gitRepo "HEAD"

def gitParseOriginRevision (gitRepo : FilePath) (rev : String) : IO String :=
  (gitParseRevision gitRepo $ "origin/" ++ rev) <|> gitParseRevision gitRepo rev
    <|> throw (IO.userError s!"cannot find revision {rev} in repository {gitRepo}")

def gitLatestOriginRevision (gitRepo : FilePath) (branch : Option String) : IO String := do
  discard <| IO.Process.run {cmd := "git", args := #["fetch"], cwd := gitRepo}
  gitParseOriginRevision gitRepo (gitdefaultRevision branch)

def gitRevisionExists (gitRepo : FilePath) (rev : String) : IO Bool := do
  try
    discard <| gitParseRevision gitRepo (rev ++ "^{commit}")
    true
  catch _ => false

end Leanpkg
