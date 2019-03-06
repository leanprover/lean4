/-
Copyright (c) 2019 Sebastian Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Sebastian Ullrich
-/
prelude
import init.lean.position init.io

namespace lean

/-- Print and accumulate run time of `act` when option `profiler` is set to `true`. -/
@[extern 5 "lean_lean_profileit"]
constant profileit {α : Type} (category : @& string) (pos : @& position) (act : io α) : io α
def profileit_pure {α : Type} (category : string) (pos : position) (fn : unit → α) : io α :=
profileit category pos $ io.lazy_pure fn

end lean
