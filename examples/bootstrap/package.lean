import Lake.Package

open Lake System

def package : PackageConfig := {
  name := "lake"
  version := "2.0-pre-bootstrap"
  rootDir := FilePath.mk ".." / ".."
  oleanDir := defaultBuildDir
  linkArgs :=
    if Platform.isWindows then
      #["-Wl,--export-all"]
    else
      #["-rdynamic"]
}
