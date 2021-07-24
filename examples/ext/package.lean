import Lake.Build
import Lake.Package
open Lake System

def extDir : FilePath := "ext"
def addSrc := extDir / "add.cpp"

def buildDir := defaultBuildDir
def addO := buildDir / extDir / "add.o"
def extLib := buildDir / extDir / "libext.a"

def fetchAddOTarget : IO FileTarget := do
  skipIfNewer addO (← getMTime addSrc) <|
    BuildTask.spawn <| compileO addO addSrc (cmd := "c++")

def fetchExtLibTarget : IO FileTarget := do
  let oTarget ← fetchAddOTarget
  skipIfNewer extLib oTarget.mtime <|
    oTarget >> compileStaticLib extLib #[addO]

def package : PackageConfig := {
  name := "ext"
  version := "0.1"
  -- customize layout
  srcDir := "lib"
  moduleRoot := `Add
  binName := "add"
  -- specify path to the lib for linker
  linkArgs := #[extLib.toString]
  -- specify the lib target as an additional dependency
  buildMoreDepsTarget := fetchExtLibTarget.map fun target =>
    LeanTarget.fromMTimeTarget <| target.discardArtifact
}
