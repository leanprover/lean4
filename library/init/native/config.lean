/-
Copyright (c) 2016 Jared Roesch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jared Roesch
-/
prelude
import init.data.bool.basic

namespace native

-- eventually expose all the options here
record config :=
  (debug : bool)

end native
