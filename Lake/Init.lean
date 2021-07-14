/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner, Sebastian Ullrich, Mac Malone
-/
import Lake.Git
import Lake.LeanConfig

namespace Lake

def initGitignoreContents :=
"/build
"

def mainFileContents :=
"def main : IO Unit :=
  IO.println \"Hello, world!\"
"

def leanPkgFileContents (pkgName : String) :=
s!"import Lake.Package

def package : Lake.PackageConfig := \{
  name := \"{pkgName}\"
  version := \"0.1\"
  leanVersion := \"{leanVersionString}\"
}
"

open Git in
def init (pkgName : String) : IO Unit := do
  IO.FS.writeFile leanPkgFile (leanPkgFileContents pkgName)
  IO.FS.writeFile ⟨s!"{pkgName.capitalize}.lean"⟩ mainFileContents
  let h ← IO.FS.Handle.mk ⟨".gitignore"⟩ IO.FS.Mode.append (bin := false)
  h.putStr initGitignoreContents
  unless ← System.FilePath.isDir ⟨".git"⟩ do
    (do
      quietInit
      unless upstreamBranch = "master" do
        checkoutBranch upstreamBranch
    ) <|>
      IO.eprintln "WARNING: failed to initialize git repository"
