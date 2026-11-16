/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
module

prelude
public import Init.Prelude

public section

namespace Lean

/-- A module that the stage0 compiler has no native code for. -/
def nativeInitProbe : Nat := 0

end Lean
