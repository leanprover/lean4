import Lake

open System Lake DSL

package test where
  releaseRepo := ""
  buildArchive := ""
  testDriver := "b"
  lintDriver := "b"
  platformIndependent := true

require "foo" / baz @ "git#abcdef"

require foo from "-" with Lake.NameMap.empty |>.insert `foo "bar"

require bar from git "https://example.com"@"abc"/"sub/dir"

@[default_target] lean_lib A

lean_exe b
