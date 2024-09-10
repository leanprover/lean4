import Lake
open Lake DSL

package dep where
  preferReleaseBuild := true
  releaseRepo := "https://example.com"
  buildArchive := "release.tgz"
