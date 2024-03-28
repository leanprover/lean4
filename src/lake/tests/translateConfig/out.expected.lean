import Lake

open System Lake DSL

package test where
  releaseRepo := ""
  buildArchive := ""
  platformIndependent := true

require foo from "-" with Lake.NameMap.empty |>.insert `foo "bar"

require bar from git "https://example.com"@"abc"/"sub/dir"

lean_lib A

@[default_target] lean_exe b
