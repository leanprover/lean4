import Lake

open System Lake DSL

package test where
  releaseRepo := ""
  buildArchive := ""
  platformIndependent := true

require foo from "-"

require bar from git "https://example.com"

lean_lib A

@[default_target] lean_exe b
