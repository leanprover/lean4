/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
prelude
import Std.Time.Internal
import Std.Time.DateTime
import Std.Time.Time

namespace Std
namespace Time
open Internal

set_option linter.all true

/--
Duration is just a period between two timestamps.
-/
def Duration := Timestamp

namespace Duration

/--
Calculates a `Duration` out of two `Timestamp`s.
-/
def since (f : Timestamp) (t : Timestamp) : Duration :=
  t.sub f
