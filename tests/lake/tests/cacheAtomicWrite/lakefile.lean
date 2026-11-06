import Lake
open System Lake DSL

/-!
Test that publication ignores temporary files owned by another publisher.
-/

package test where
  enableArtifactCache := true

target text pkg : FilePath := Job.async <| withCurrPackage pkg do
  let file := pkg.buildDir / "text.txt"
  let art ← buildArtifactUnlessUpToDate file (text := true) do
    createParentDirs file
    copyFile (pkg.dir / "fixtures" / "source.txt") file
  return art.path
