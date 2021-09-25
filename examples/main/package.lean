import Lake

def package : Lake.PackageConfig := {
  name := "foo"
  libRoots := #[`Lib]
  binRoot := `Main
}
