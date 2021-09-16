import Lake.Package

def package : Lake.PackageConfig := {
  name := "foo"
  version := "1.0"
  moduleRoot := `Lib
  binRoot := `Main
}
