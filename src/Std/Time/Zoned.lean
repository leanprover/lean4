/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
prelude
import Std.Time.Zoned.DateTime
import Std.Time.Zoned.ZoneRules
import Std.Time.Zoned.ZonedDateTime
import Std.Time.Zoned.Database.Basic

namespace Std
namespace Time
namespace TimeZone
namespace ZoneRules

/--
Parses a binary data into a zone rules.
-/
def parseTZif (bin : ByteArray) : Except String ZoneRules := do
  let database ← Database.TZif.TZif.parse.run bin
  Database.convertTZif database

/--
Gets the ZoneRules from the a TZIf file.
-/
def parseTZIfFromDisk (path : System.FilePath) : IO ZoneRules := do
  let binary ← IO.FS.readBinFile path
  IO.ofExcept (parseTZif binary)

/--
Gets the rules from local timezone.
-/
def localRules : IO ZoneRules := do
  parseTZIfFromDisk "etc/localtime"

/--
Gets the rules from local timezone.
-/
def readRulesFromDisk (id : String) : IO ZoneRules := do
  parseTZIfFromDisk (System.FilePath.join "/usr/share/zoneinfo/" id)

end ZoneRules
end TimeZone
end Time
end Std
