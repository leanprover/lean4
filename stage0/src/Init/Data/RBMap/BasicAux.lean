/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Data.RBMap.Basic
import Init.Util

universes u v w w'

namespace RBMap
variables {α : Type u} {β : Type v} {lt : α → α → Bool}

@[inline] def min! [Inhabited α] [Inhabited β] (t : RBMap α β lt) : α × β :=
match t.min with
| some p => p
| none   => panic! "map is empty"

@[inline] def max! [Inhabited α] [Inhabited β] (t : RBMap α β lt) : α × β :=
match t.max with
| some p => p
| none   => panic! "map is empty"

@[inline] def find! [Inhabited β] (t : RBMap α β lt) (k : α) : β :=
match t.find? k with
| some b => b
| none   => panic! "key is not in the map"

end RBMap
