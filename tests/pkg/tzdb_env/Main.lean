import Std.Time
open Std.Time

def main : IO Unit := do
  let res ← Database.defaultGetLocalZoneRules
  println! repr res.initialLocalTimeType.gmtOffset
