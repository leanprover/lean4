/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
public import Std.Time.Zoned.Database.Basic
import Init.Data.String.TakeDrop

public section

namespace Std
namespace Time
namespace Database

set_option linter.all true

/--
Represents a Time Zone Database (TZdb) configuration with paths to local and general timezone data.
-/
structure TZdb where

  /--
  Static fallback paths to directories containing time zone files. `TZDIR` is not stored here;
  it is re-read on every lookup via `resolveZonesPaths`.
  -/
  zonesPaths : Array System.FilePath

namespace TZdb
open TimeZone

/--
Parses binary timezone data into zone rules based on a given timezone ID.
-/
def parseTZif (bin : ByteArray) (id : String) : Except String ZoneRules := do
  let database ← TZif.parse.run bin
  convertTZif database id

/--
Reads a TZif file from disk and retrieves the zone rules for the specified timezone ID.
-/
def parseTZIfFromDisk (path : System.FilePath) (id : String) : IO ZoneRules := do
  let binary ← try IO.FS.readBinFile path catch _ => throw <| IO.userError s!"unable to locate {id} in the local timezone database at '{path}'"
  IO.ofExcept (parseTZif binary id)

/--
Extracts a timezone ID from a file path.
-/
def idFromPath (path : System.FilePath) : Option String := do
  let res := path.components.toArray
  let last ← res[res.size - 1]?
  let last₁ ← res[res.size - 2]?

  if last₁ = "zoneinfo"
    then some <| last.trimAscii.copy
    else some <| last₁.trimAscii.copy ++ "/" ++ last.trimAscii

/--
Retrieves the timezone rules from the local timezone data file.
-/
def localRules (path : System.FilePath) : IO ZoneRules := do
  let localTimePath ← IO.FS.realPath path
  if let some id := idFromPath localTimePath
    then parseTZIfFromDisk path id
    else throw (IO.userError "cannot read the id of the path.")

/--
Reads timezone rules from disk based on the provided file path and timezone ID.
-/
def readRulesFromDisk (path : System.FilePath) (id : String) : IO ZoneRules := do
  parseTZIfFromDisk (path.join id) id

/--
Parsed form of the `TZ` environment variable.

The POSIX proleptic format (e.g. `TZ=EST5EDT,M3.2.0,M11.1.0`) is not supported;
only file paths and timezone IDs backed by zoneinfo data are recognized.
-/
inductive TZSpec

  /--
  A file path (the part after the leading `:`), absolute or relative to a zoneinfo directory.
  -/
  | filePath (p : String)

  /--
  A timezone ID such as `America/New_York`, looked up in the zoneinfo search paths.
  -/
  | zoneId (id : String)
deriving Repr, BEq

/--
Parses the value of the `TZ` environment variable. Returns `none` for empty or
`:` (empty path after the colon) values.
-/
def parseTZValue (tz : String) : Option TZSpec :=
  if tz.startsWith ":" then
    let p := (tz.drop 1).toString
    if p.isEmpty then none else some (.filePath p)
  else if !tz.isEmpty then
    some (.zoneId tz)
  else
    none

/--
Returns the first path in `searchPaths` joined with `rel` that exists on disk, or `none`.
-/
def findInPaths (searchPaths : Array System.FilePath) (rel : String) : IO (Option System.FilePath) := do
  for base in searchPaths do
    let full := base.join rel
    if ← full.pathExists then
      return some full

  return none

/--
Resolves the local timezone file path from the `TZ` environment variable, searching
`zonesPaths` for relative paths and timezone IDs. Falls back to `/etc/localtime` if
`TZ` is unset. Throws if `TZ` is set but its value cannot be found on disk.
-/
def resolveLocalPath (zonesPaths : Array System.FilePath) : IO System.FilePath := do
  let some tz ← IO.getEnv "TZ"
    | return "/etc/localtime"

  let some spec := parseTZValue tz
    | return "/etc/localtime"

  match spec with
  | .filePath p =>
    if p.startsWith "/" then return p
    if let some path ← findInPaths zonesPaths p then return path
    throw <| IO.userError s!"TZ='{tz}': path '{p}' not found in any zoneinfo directory"
  | .zoneId id =>
    if let some path ← findInPaths zonesPaths id then return path
    throw <| IO.userError s!"TZ='{tz}': timezone not found in any zoneinfo directory"

/--
Returns a `TZdb` with common fallback zoneinfo paths for Linux and macOS.
Call this once at program startup. The `TZ` and `TZDIR` environment variables
are re-read on every `getLocalZoneRules`/`getZoneRules` call, so runtime changes
to those variables are always reflected.
-/
def default : TZdb where
  zonesPaths := #["/usr/share/zoneinfo", "/share/zoneinfo", "/etc/zoneinfo", "/usr/share/lib/zoneinfo"]

/--
Builds the effective zoneinfo search path by prepending the current `TZDIR` (if set and
exists on disk) to `db.zonesPaths`. Called on every lookup so that runtime changes to
`TZDIR` are reflected immediately.
-/
def resolveZonesPaths (db : TZdb) : IO (Array System.FilePath) := do
  match ← IO.getEnv "TZDIR" with
  | none | some "" => return db.zonesPaths
  | some d =>
    if ← System.FilePath.pathExists d then return (#[(d : System.FilePath)] ++ db.zonesPaths)
    else return db.zonesPaths

/--
Retrieves the timezone rules for the local timezone, re-reading the `TZ` and `TZDIR`
environment variables on each call so that runtime changes are reflected immediately.
-/
def getLocalZoneRules (db : TZdb) : IO ZoneRules := do
  let path ← resolveLocalPath (← db.resolveZonesPaths)
  localRules path

/--
Retrieves the timezone rules for the given timezone ID, re-reading `TZDIR` on each
call so that runtime changes are reflected immediately.
-/
def getZoneRules (db : TZdb) (id : String) : IO ZoneRules := do
  for base in ← db.resolveZonesPaths do
    if ← (base.join id).pathExists then
      return ← readRulesFromDisk base id

  throw <| IO.userError s!"cannot find {id} in the local timezone database"

instance : Std.Time.Database TZdb where
  getLocalZoneRules db := db.getLocalZoneRules
  getZoneRules db id := db.getZoneRules id
