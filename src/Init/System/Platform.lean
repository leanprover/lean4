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

/--
Checks whether the current platform is Windows.
-/
@[extern "lean_system_platform_windows"] opaque getIsWindows : Unit → Bool
/--
Checks whether the current platform is macOS.
-/
@[extern "lean_system_platform_osx"] opaque getIsOSX : Unit → Bool
/--
Checks whether the current platform is [Emscripten](https://emscripten.org/).
-/
@[extern "lean_system_platform_emscripten"] opaque getIsEmscripten : Unit → Bool

/--
Is the current platform Windows?
-/
def isWindows : Bool := getIsWindows ()

/--
Is the current platform macOS?
-/
def isOSX : Bool := getIsOSX ()

/--
Is the current platform [Emscripten](https://emscripten.org/)?
-/
def isEmscripten : Bool := getIsEmscripten ()

/--
Gets the LLVM target triple of the current platform, or `""` if this was missing when Lean was
compiled.
-/
@[extern "lean_system_platform_target"] opaque getTarget : Unit → String

/--
The LLVM target triple of the current platform. Empty if missing when Lean was compiled.
-/
def target : String := getTarget ()

theorem numBits_pos : 0 < numBits := by
  cases numBits_eq <;> next h => simp [h]

@[simp]
theorem le_numBits : 32 ≤ numBits := by
  cases numBits_eq <;> next h => simp [h]

@[simp]
theorem numBits_le : numBits ≤ 64 := by
  cases numBits_eq <;> next h => simp [h]

@[simp] theorem eight_le_numBits : 8 ≤ System.Platform.numBits := by
  cases System.Platform.numBits_eq <;> simp_all
@[simp] theorem sixteen_le_numBits : 16 ≤ System.Platform.numBits := by
  cases System.Platform.numBits_eq <;> simp_all

@[simp] theorem eight_dvd_numBits : 8 ∣ System.Platform.numBits :=
  numBits_eq.elim (fun h => ⟨4, h ▸ rfl⟩) (fun h => ⟨8, h ▸ rfl⟩)
@[simp] theorem System.Platform.sixteen_dvd_numBits : 16 ∣ System.Platform.numBits :=
  numBits_eq.elim (fun h => ⟨2, h ▸ rfl⟩) (fun h => ⟨4, h ▸ rfl⟩)
@[simp] theorem System.Platform.dvd_numBits : 32 ∣ System.Platform.numBits :=
  numBits_eq.elim (fun h => ⟨1, by simp [h]⟩) (fun h => ⟨2, h ▸ rfl⟩)
@[simp] theorem System.Platform.numBits_dvd : System.Platform.numBits ∣ 64 :=
  numBits_eq.elim (fun h => ⟨2, h ▸ rfl⟩) (fun h => ⟨1, by simp [h]⟩)

instance : NeZero System.Platform.numBits where
  out := Nat.ne_zero_of_lt System.Platform.numBits_pos

end Platform
end System
