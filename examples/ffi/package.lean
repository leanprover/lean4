import Lake.Package
import Lake.BuildTargets

open Lake System

def cDir : FilePath := "c"
def addSrc := cDir / "add.cpp"

def buildDir := defaultBuildDir
def addO := buildDir / cDir / "add.o"
def cLib := buildDir / cDir / "libadd.a"

def addOTarget : FileTarget := do
  oFileTarget addO addSrc

def cLibTarget : FileTarget := do
  staticLibTarget cLib #[addOTarget]

def package : PackageConfig := {
  name := "ffi"
  version := "0.1"
  -- customize layout
  srcDir := "lib"
  moduleRoot := `Add
  binName := "add"
  -- specify the lib as an additional target
  moreLibTargets := #[cLibTarget]
}
