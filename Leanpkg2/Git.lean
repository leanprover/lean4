/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner, Sebastian Ullrich, Mac Malone
-/
import Leanpkg2.Proc
import Leanpkg2.LeanVersion

open System

namespace Leanpkg2.Git

def upstreamBranch :=
  "master"

def defaultRevision : Option String → String
  | none => upstreamBranch
  | some branch => branch

def clone (url : String) (dir : FilePath) :=
  execCmd {cmd := "git", args := #["clone", url, dir.toString]}

def quietInit (repo : Option FilePath := none) :=
  execCmd {cmd := "git", args := #["init", "-q"]}

def fetch (repo : Option FilePath := none) :=
  execCmd {cmd := "git", args := #["fetch"], cwd := repo}

def checkoutBranch (branch : String) (repo : Option FilePath := none) :=
  execCmd {cmd := "git", args := #["checkout", "-B", branch]}

def checkoutDetach (hash : String) (repo : Option FilePath := none)  :=
  execCmd {cmd := "git", args := #["checkout", "--detach", hash], cwd := repo}

def parseRevision (rev : String) (repo : Option FilePath := none) : IO String := do
  let rev ← IO.Process.run {cmd := "git", args := #["rev-parse", "-q", "--verify", rev], cwd := repo}
  rev.trim -- remove newline at end

def headRevision (repo : Option FilePath := none) : IO String :=
  parseRevision "HEAD" repo

def parseOriginRevision (rev : String) (repo : Option FilePath := none) : IO String :=
  (parseRevision ("origin/" ++ rev) repo) <|> parseRevision rev repo
    <|> throw (IO.userError s!"cannot find revision {rev} in repository {repo}")

def latestOriginRevision (branch : Option String) (repo : Option FilePath := none) : IO String := do
  discard <| IO.Process.run {cmd := "git", args := #["fetch"], cwd := repo}
  parseOriginRevision (defaultRevision branch) repo

def revisionExists (rev : String) (repo : Option FilePath := none) : IO Bool := do
  try
    discard <| parseRevision (rev ++ "^{commit}") repo
    true
  catch _ => false
