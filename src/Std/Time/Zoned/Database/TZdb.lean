/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
prelude
import Std.Time.DateTime
import Std.Time.Zoned.TimeZone
import Std.Time.Zoned.ZoneRules
import Std.Time.Zoned.Database.Basic

namespace Std
namespace Time
namespace Database

set_option linter.all true

/--
Represents a Time Zone Database (TZdb) configuration with paths to local and general timezone data.
-/
structure TZdb where

  /--
  The path to the local timezone file. This is typically a symlink to a file within the timezone
  database that corresponds to the current local time zone.
  -/
  localPath : System.FilePath := "/etc/localtime"

  /--
  All the possible paths to the directories containing all available time zone files. These files define various
  time zones and their rules.
  -/
  zonesPaths : Array System.FilePath := #["/usr/share/zoneinfo", "/share/zoneinfo", "/etc/zoneinfo", "/usr/share/lib/zoneinfo"]

namespace TZdb
open TimeZone

/--
Returns a default `TZdb` instance with common timezone data paths for most Linux distributions and macOS.
-/
@[inline]
def default : TZdb := {}

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

  if last₁ = some "zoneinfo"
    then last.trim
    else last₁.trim ++ "/" ++ last.trim

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
  parseTZIfFromDisk (System.FilePath.join path id) id

instance : Std.Time.Database TZdb where
  getLocalZoneRules db := localRules db.localPath

  getZoneRules db id := do
    let env ← IO.getEnv "TZDIR"

    if let some path := env then
      let result ← readRulesFromDisk path id
      return result

    for path in db.zonesPaths do
      if ← System.FilePath.pathExists path then
        let result ← readRulesFromDisk path id
        return result

    throw <| IO.userError s!"cannot find {id} in the local timezone database"
