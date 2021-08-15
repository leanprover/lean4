import Lake.Package
import Lake.BuildTargets

open Lake System

def cDir : FilePath := "c"
def addSrc := cDir / "add.cpp"

def buildDir := defaultBuildDir
def addO := buildDir / cDir / "add.o"
def cLib := buildDir / cDir / "libadd.a"

def computeAddOTarget : IO FileTarget := do
  oFileTarget addO <| ← FileTarget.compute addSrc

def computeCLibTarget : IO FileTarget := do
  staticLibTarget cLib <| ← computeAddOTarget

def package : PackageConfig := {
  name := "ffi"
  version := "0.1"
  -- customize layout
  srcDir := "lib"
  moduleRoot := `Add
  binName := "add"
  -- specify the lib as an additional target
  buildMoreLibTargets := do #[← (← computeCLibTarget).runAsync]
}
