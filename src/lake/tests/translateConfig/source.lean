import Lake
open Lake DSL

def testLeanConfig : LeanConfig where
  buildType := .release
  leanOptions := #[]
  moreServerOptions := #[]
  moreLeanArgs := #[]
  weakLeanArgs := #[]
  moreLeancArgs := #[]
  weakLeancArgs := #[]
  moreLinkArgs := #[]
  weakLinkArgs := #[]
  backend := .default
  platformIndependent := none

package test where
  extraDepTargets := #[]
  precompileModules := false
  moreGlobalServerArgs := #[]
  srcDir := "."
  buildDir := defaultBuildDir
  leanLibDir := defaultLeanLibDir
  nativeLibDir := defaultNativeLibDir
  binDir := defaultBinDir
  irDir := defaultIrDir
  releaseRepo := none
  releaseRepo? := none
  buildArchive? := none
  preferReleaseBuild := false
  packagesDir := defaultPackagesDir
  toLeanConfig := testLeanConfig

require foo from "dir" with NameMap.empty.insert `foo "bar"
require bar from git "https://example.com" @ "abc" / "sub" / "dir"

lean_lib A where
  srcDir := "."
  roots := #[`A]
  globs := #[`A]
  extraDepTargets := #[]
  precompileModules := false
  defaultFacets := #[LeanLib.leanArtsFacet]
  nativeFacets := fun _ => #[]
  toLeanConfig := testLeanConfig

@[default_target]
lean_exe b where
  srcDir := "."
  root := `b
  exeName := "b"
  extraDepTargets := #[]
  supportInterpreter := false
  nativeFacets := fun _ => #[]
  toLeanConfig := testLeanConfig
