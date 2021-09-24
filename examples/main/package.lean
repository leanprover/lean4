import Lake.Package

def package : Lake.PackageConfig := {
  name := "foo"
  version := "1.0"
  libRoots := #[`Lib]
  binRoot := `Main
}
