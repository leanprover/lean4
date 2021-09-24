import Lake.Package
import Lake.BuildTargets

open Lake System

def package : PackageConfig := {
  name := "ffi-dep"
  version := "0.1"
  binRoot := `Main
  binName := "add"
  dependencies := [{
    name := "ffi"
    src := Source.path (FilePath.mk ".." / "ffi")
  }]
}
