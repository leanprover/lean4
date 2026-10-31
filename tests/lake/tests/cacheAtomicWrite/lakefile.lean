import Lake
open System Lake DSL

/-!
Test how the Lake artifact cache recovers from
a temporary file left by an interrupted write.
-/

package test where
  enableArtifactCache := true

target text pkg : FilePath := Job.async <| withCurrPackage pkg do
  let file := pkg.buildDir / "text.txt"
  let art ← buildArtifactUnlessUpToDate file (text := true) do
    createParentDirs file
    copyFile (pkg.dir / "fixtures" / "source.txt") file
  return art.path
