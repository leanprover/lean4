import Lake
open System Lake DSL

/-!
Test how the Lake artifact cache recovers from
a temporary file left by an interrupted write or download.
-/

package test where
  enableArtifactCache := true

target text pkg : FilePath := Job.async <| withCurrPackage pkg do
  let file := pkg.buildDir / "text.txt"
  let art ← buildArtifactUnlessUpToDate file (text := true) do
    createParentDirs file
    copyFile (pkg.dir / "fixtures" / "source.txt") file
  return art.path

/--
Downloads the fixture `NAME` via a `file://` URL as the artifact
for `fixtures/source.txt` at `PATH`.
-/
script download (args) do
  let [name, path] := args
    | throw <| IO.userError "expected NAME PATH"
  let hash := Hash.ofByteArray (← IO.FS.readBinFile ("fixtures" / "source.txt"))
  let file ← IO.FS.realPath ("fixtures" / name)
  let file := "/".intercalate (file.components.map uriEncode)
  -- Windows paths start with a drive letter, which needs a leading `/` in a URL
  let file := if file.startsWith "/" then file else "/" ++ file
  let url := s!"file://{file}"
  let ok ← (downloadArtifactCore hash url path).toBaseIO
  return if ok.isSome then 0 else 1
