/-
Copyright (c) 2016 Jared Roesch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jared Roesch
-/
prelude

import init.meta.name
import init.meta.expr

meta def procedure :=
name × expr

meta def procedure.repr : procedure → string
| (n, e) := "def " ++ repr n ++ " := \n" ++ repr e

meta def procedure.map_body (f : expr → expr) : procedure → procedure
| (n, e) := (n, f e)

meta instance : has_repr procedure :=
⟨procedure.repr⟩
