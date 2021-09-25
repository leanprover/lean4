import Lake
open Lake System

def package : PackageConfig := {
  name := "ffi-dep"
  binRoot := `Main
  binName := "add"
  dependencies := [{
    name := "ffi"
    src := Source.path (FilePath.mk ".." / "ffi")
  }]
}
