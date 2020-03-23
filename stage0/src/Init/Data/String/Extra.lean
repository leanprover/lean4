/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
prelude
import Init.Util

namespace String

def toNat! (s : String) : Nat :=
if s.isNat then
  s.foldl (fun n c => n*10 + (c.toNat - '0'.toNat)) 0
else
  panic! "Nat expected"

end String
