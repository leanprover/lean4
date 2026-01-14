/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Grove.Framework
import GroveStdlib.Std.Libraries.DateAndTime
import GroveStdlib.Std.Libraries.RandomNumbers

open Grove.Framework Widget

namespace GroveStdlib.Std

namespace Libraries

end Libraries

def libraries : Node :=
  .section "libraries" "Libraries" #[
    Libraries.dateAndTime,
    Libraries.randomNumbers
  ]

end GroveStdlib.Std
