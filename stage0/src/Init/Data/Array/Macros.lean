/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.LeanInit
import Init.Data.Array.Basic
import Init.Data.Array.Subarray
new_frontend

namespace Array

syntax:max term noWs "[" term ":" term "]" : term
syntax:max term noWs "[" term ":" "]" : term
syntax:max term noWs "[" ":" term "]" : term

macro_rules
| `($a[$start : $stop]) => `(Array.toSubarray $a $start $stop)
| `($a[ : $stop])       => `(Array.toSubarray $a 0 $stop)
| `($a[$start : ])      => `(let a := $a; Array.toSubarray a $start a.size)

end Array
