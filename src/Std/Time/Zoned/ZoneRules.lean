/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
prelude
import Std.Time.Time
import Std.Time.DateTime
import Std.Time.Internal

namespace Std
namespace Time
namespace TimeZone
open Internal

/--
Represents the type of local time in relation to UTC.
-/
inductive UTLocal
  | ut
  | local
  deriving Repr, Inhabited

/--
Represents types of wall clocks or standard times.
-/
inductive StdWall
  | wall
  | standard
  deriving Repr, Inhabited

/--
Represents a type of local time, including offset and daylight saving information.
-/
structure LocalTimeType where
  gmtOffset : Second.Offset
  isDst : Bool
  abbreviation : String
  wall : StdWall
  utLocal : UTLocal
  deriving Repr, Inhabited

/--
Represents a leap second event, including the time of the transition and the correction applied.
-/
structure LeapSecond where
  transitionTime : Second.Offset
  correction : Second.Offset
  deriving Repr, Inhabited

/--
Represents a time zone transition, mapping a time to a local time type.
-/
structure Transition where
  time : Second.Offset
  localTimeType : LocalTimeType
  deriving Repr, Inhabited

/--
Represents the rules for a time zone, abstracting away binary data and focusing on key transitions and types.
-/
structure ZoneRules where
  transitions : Array Transition
  leapSeconds : Array LeapSecond
  deriving Repr, Inhabited


namespace ZoneRules

/--
Finds the transition corresponding to a given timestamp in `ZoneRules`.
If the timestamp falls between two transitions, it returns the most recent transition before the timestamp.
-/
def findTransitionForTimestamp (zoneRules : ZoneRules) (timestamp : Timestamp) : Option Transition :=
  if let some idx := zoneRules.transitions.findIdx? (λ t => t.time.val > timestamp.val)
    then zoneRules.transitions.get? (idx - 1)
    else zoneRules.transitions.back?

/--
Apply leap seconds to a Timestamp
-/
def applyLeapSeconds (timeInSeconds : Timestamp) (leapSeconds : Array LeapSecond) : Timestamp := Id.run do
  let mut currentTime := timeInSeconds
  for i in [:leapSeconds.size] do
    let leapSec := leapSeconds.get! i
    if currentTime.val >= leapSec.transitionTime.val then
      currentTime := ⟨currentTime.val + leapSec.correction.val⟩
  return currentTime
