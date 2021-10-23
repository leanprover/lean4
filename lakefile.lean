import Lake
open System Lake DSL

package lake where
  binRoot := `Lake.Main
  moreLinkArgs := if Platform.isWindows then #[] else #["-rdynamic"]
