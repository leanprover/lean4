/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner, Sebastian Ullrich, Mac Malone
-/
import Leanpkg2.Git
import Leanpkg2.Proc
import Leanpkg2.Manifest

namespace Leanpkg2

def initGitignoreContents :=
"/build
"

def mainFileContents :=
"def main : IO Unit :=
  IO.println \"Hello, world!\"
"

def leanpkgFileContents (pkgName : String) :=
s!"[package]
name = \"{pkgName}\"
version = \"0.1\"
lean_version = \"{leanVersionString}\"
"

def initPkg (pkgName : String) (fromNew : Bool) : IO Unit := do
  IO.FS.writeFile leanpkgTomlFn (leanpkgFileContents pkgName)
  IO.FS.writeFile ⟨s!"{pkgName.capitalize}.lean"⟩ mainFileContents
  let h ← IO.FS.Handle.mk ⟨".gitignore"⟩ IO.FS.Mode.append (bin := false)
  h.putStr initGitignoreContents
  unless ← System.FilePath.isDir ⟨".git"⟩ do
    (do
      execCmd {cmd := "git", args := #["init", "-q"]}
      unless upstreamGitBranch = "master" do
        execCmd {cmd := "git", args := #["checkout", "-B", upstreamGitBranch]}
    ) <|> IO.eprintln "WARNING: failed to initialize git repository"

def init (pkgName : String) := initPkg pkgName false
