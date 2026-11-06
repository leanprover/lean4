import Lake.Config.Cache
import Lake.Build.Common

/-! Exercise shared-cache integration through existing Lake artifact APIs. -/

open System Lake

def main (args : List String) : IO UInt32 := do
  match args with
  | ["restore-exe", root, source, target] =>
    let artifact ← (Cache.mk root).saveArtifact source "exe"
    let result ← (restoreArtifact target artifact (exe := true)).toBaseIO
    return if result.isSome then 0 else 1
  | ["map", path, contents] =>
    let artifact := artifactWithExt (Hash.ofByteArray contents.toUTF8) "art"
    let map := ({} : CacheMap).insert (Hash.ofString "input") artifact
    let result ← (map.writeFile path).toBaseIO
    return if result.isSome then 0 else 1
  | _ => throw <| IO.userError "expected restore-exe CACHE SOURCE TARGET or map PATH CONTENTS"
