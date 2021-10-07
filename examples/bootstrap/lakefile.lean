import Lake
open System Lake DSL

package lake where
  srcDir := FilePath.mk ".." / ".."
  oleanDir := "."
  binRoot := `Lake.Main
  moreLinkArgs :=
    if Platform.isWindows then
      #["-Wl,--export-all"]
    else
      #["-rdynamic"]
