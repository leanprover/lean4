/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Data.Nat.Basic
import Init.Data.String.Basic

namespace System
namespace Platform

@[extern "lean_system_platform_windows"] opaque getIsWindows : Unit → Bool
@[extern "lean_system_platform_osx"] opaque getIsOSX : Unit → Bool
@[extern "lean_system_platform_emscripten"] opaque getIsEmscripten : Unit → Bool

def isWindows : Bool := getIsWindows ()
def isOSX : Bool := getIsOSX ()
def isEmscripten : Bool := getIsEmscripten ()

@[extern "lean_system_platform_target"] opaque getTarget : Unit → String

/-- The LLVM target triple of the current platform. Empty if missing at Lean compile time. -/
def target : String := getTarget ()

theorem numBits_pos : 0 < numBits := by
  cases numBits_eq <;> next h => simp [h]

theorem le_numBits : 32 ≤ numBits := by
  cases numBits_eq <;> next h => simp [h]

theorem numBits_le : numBits ≤ 64 := by
  cases numBits_eq <;> next h => simp [h]

end Platform
end System
