import Lake
open System Lake DSL

package where
  name := "lake"
  srcDir := FilePath.mk ".." / ".."
  oleanDir := "."
  leancArgs := #["-O3", "-DNDEBUG"]
  binRoot := `Lake.Main
  linkArgs :=
    if Platform.isWindows then
      #["-Wl,--export-all"]
    else
      #["-rdynamic"]
