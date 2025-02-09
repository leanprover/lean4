/-
Copyright (c) 2024 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: François G. Dorais
-/
prelude
import Init.Data.List.FinRange

namespace Array

/-- `finRange n` is the array of all elements of `Fin n` in order. -/
protected def finRange (n : Nat) : Array (Fin n) := ofFn fun i => i

end Array
