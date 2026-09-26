import Lean
open Lean System

/-! `findOLean` caches, per root package, the search path entry that contains it. -/

/--
info: first lookup caches the package: true
second lookup is served from the cache: true
a new search path discards the cache: true
-/
#guard_msgs in
#eval show IO Unit from do
  let sp ← searchPathRef.get
  let expected ← findOLean `Lean.Environment
  try
    oleanRootCacheRef.set ([], [])
    discard <| findOLean `Lean.Util.Path
    let (cachedSp, cache) ← oleanRootCacheRef.get
    IO.println s!"first lookup caches the package: {cachedSp == sp && cache.map (·.1) == [`Lean]}"
    -- a hit must not look at the search path, so it returns whatever root is cached
    oleanRootCacheRef.set (sp, [(`Lean, "sentinel")])
    let hit ← findOLean `Lean.Environment
    IO.println s!"second lookup is served from the cache: {hit == modToFilePath "sentinel" `Lean.Environment "olean"}"
    -- like Lake, which sets `searchPathRef` directly
    searchPathRef.set ("extra" :: sp)
    let miss ← findOLean `Lean.Environment
    IO.println s!"a new search path discards the cache: {miss == expected}"
  finally
    searchPathRef.set sp
