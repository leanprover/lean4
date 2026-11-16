import Lake

open System Lake DSL

package test where
  releaseRepo := ""
  buildArchive := ""
  downloadCacheService := "cdn"
  testDriver := "b"
  lintDriver := "b"
  enableArtifactCache := false
  restoreAllArtifacts := false
  builtinLint := false
  platformIndependent := true

require "foo" / baz @ git "abcdef"

require foo from "-" with Lake.NameMap.empty |>.insert `foo "bar"

require bar from git "https://example.com"@"abc"/"sub/dir"

require qux from copy "qux"

cache_service cdn :=
  .downloadService "https://example.com/a0" "https://example.com/r0" (hasPackageScopes := false)

cache_service «my-reservoir» :=
  .reservoirService "https://example.com/api/v1"

@[default_target] lean_lib A

lean_exe b
