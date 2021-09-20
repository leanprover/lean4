import Lake.Package
import Lake.BuildTargets

open Lake System

def cDir : FilePath := "c"
def addSrc := cDir / "add.cpp"

def buildDir := defaultBuildDir
def addO := buildDir / cDir / "add.o"
def cLib := buildDir / cDir / "libadd.a"

def addOTarget (pkgDir : FilePath) : FileTarget :=
  oFileTarget (pkgDir / addO) (pkgDir / addSrc : FilePath)

def cLibTarget (pkgDir : FilePath) : FileTarget :=
  staticLibTarget (pkgDir / cLib) #[addOTarget pkgDir]

def package : Packager := fun pkgDir args => {
  name := "ffi"
  version := "0.1"
  -- customize layout
  srcDir := "lib"
  moduleRoot := `Add
  binName := "add"
  binRoot := `Main
  -- specify the lib as an additional target
  moreLibTargets := #[cLibTarget pkgDir]
}
