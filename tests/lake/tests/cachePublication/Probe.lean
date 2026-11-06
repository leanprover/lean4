import Lake.Config.Cache
import Lake.Build.Common

/-! Exercise cache publication through the native Lake implementation. -/

open System Lake

def main (args : List String) : IO UInt32 := do
  match args with
  | ["fetch", url, path, contents] =>
    let result ← (downloadArtifactCore (Hash.ofByteArray contents.toUTF8) url path).toBaseIO
    return if result.isSome then 0 else 1
  | ["save", root, source] =>
    let artifact ← (Cache.mk root).saveArtifact source "art"
    IO.println artifact.path
    return 0
  | ["save-text", root, source] =>
    let artifact ← (Cache.mk root).saveArtifact source "art" (text := true)
    IO.println artifact.path
    return 0
  | ["batch", url, root, contents] =>
    let hash := Hash.ofByteArray contents.toUTF8
    let result ← (CacheService.downloadArtifacts #[artifactWithExt hash "art"] ⟨root⟩
      (CacheService.downloadArtsService url) (.ofString "test")).toBaseIO
    return if result.isSome then 0 else 1
  | ["batch-extra", url, root, contents] =>
    let hash := Hash.ofByteArray contents.toUTF8
    let result ← (CacheService.downloadArtifacts
      #[artifactWithExt hash "art", artifactWithExt hash "extra"] ⟨root⟩
      (CacheService.downloadArtsService url) (.ofString "test")).toBaseIO
    return if result.isSome then 0 else 1
  | ["metadata", root, value] =>
    let cache := Cache.mk root
    let payload := Lean.Json.str (String.ofList (List.replicate 65536 value.toList.head!))
    for _ in [:40] do
      cache.writeOutputs "fixture" (Hash.ofString "input") payload
      IO.sleep 1
    return 0
  | _ => throw <| IO.userError "expected fetch URL PATH CONTENTS or save ROOT SOURCE"
