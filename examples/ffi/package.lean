import Lake.Build
import Lake.Package
open Lake System

def cDir : FilePath := "c"
def addSrc := cDir / "add.cpp"

def buildDir := defaultBuildDir
def addO := buildDir / cDir / "add.o"
def cLib := buildDir / cDir / "libadd.a"

def fetchAddOTarget : IO ActiveFileTarget := do
  skipIfNewer addO (← getMTime addSrc) <|
    BuildTask.spawn <| compileO addO addSrc (cmd := "c++")

def fetchCLibTarget : IO ActiveFileTarget := do
  let oTarget ← fetchAddOTarget
  skipIfNewer cLib oTarget.mtime <|
    oTarget >> compileStaticLib cLib #[addO]

def package : PackageConfig := {
  name := "ffi"
  version := "0.1"
  -- customize layout
  srcDir := "lib"
  moduleRoot := `Add
  binName := "add"
  -- specify path to the lib for linker
  linkArgs := #[cLib.toString]
  -- specify the lib target as an additional dependency
  buildMoreDepsTarget := fetchCLibTarget.map fun target =>
    LeanTarget.fromMTimeTarget <| target.discardArtifact
}
