/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
prelude
import Lean.Time.DateTime.NaiveDateTime
import Lean.Time.DateTime.Timestamp

namespace Lean
namespace DateTime.Timestamp

/--
Converts a `NaiveDateTime` to a `Timestamp`
-/
@[inline]
def ofNaiveDateTime (naive : NaiveDateTime) : Timestamp :=
  naive.toTimestamp

/--
Converts a `Timestamp` to a `NaiveDateTime`
-/
@[inline]
def toNaiveDateTime (timestamp : Timestamp) : NaiveDateTime :=
  NaiveDateTime.ofTimestamp timestamp
