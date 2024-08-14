/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
import Std.Time.Zoned.Database.Basic
import Std.Time.Zoned.ZoneRules
import Std.Time.Zoned.TimeZone
import Std.Time.DateTime

namespace Std
namespace Time
namespace Database

/--
Reads the TZDb from the system from the TZDb database usually available in ""/usr/share/zoneinfo/".",
-/
structure TZdb where
  localPath : System.FilePath := "/etc/localtime"
  zonesPath : System.FilePath := "/usr/share/zoneinfo/"

namespace TZdb
open TimeZone

/--
Returns a default TZdb with all the fields completed with the default location for timezones in most
linux distributions and MacOS.
-/
@[inline]
def default : TZdb := {}

/--
Parses a binary data into a zone rules.
-/
def parseTZif (bin : ByteArray) (id : String) : Except String ZoneRules := do
  let database ← TZif.parse.run bin
  convertTZif database id

/--
Gets the ZoneRules from the a TZIf file.
-/
def parseTZIfFromDisk (path : System.FilePath) (id : String) : IO ZoneRules := do
  let binary ← IO.FS.readBinFile path
  IO.ofExcept (parseTZif binary id)

/--
Creates an id out of a `FilePath`, e.g, "/var/db/timezone/zoneinfo/America/Sao_Paulo" returns
"America/Sao_Paulo".
-/
def idFromPath (path : System.FilePath) : Option String := do
  let res := path.components.toArray
  let last ← res.get? (res.size - 1)
  let last₁ ← res.get? (res.size - 2)

  if last₁ = some "zoneinfo"
    then last
    else last₁ ++ "/" ++ last
/--
Gets the rules from local
-/
def localRules (path : System.FilePath) : IO ZoneRules := do
  let localtimePath ← IO.Process.run { cmd := "readlink", args := #["-f", path.toString] }

  if let some id := idFromPath localtimePath
    then parseTZIfFromDisk path id
    else throw (IO.userError "cannot read the id of the path.")

/--
Gets the rules from local
-/
def readRulesFromDisk (path : System.FilePath) (id : String) : IO ZoneRules := do
  parseTZIfFromDisk (System.FilePath.join path id) id

instance : Database TZdb where
  load db id := readRulesFromDisk db.zonesPath id
  localRules db := localRules db.localPath
