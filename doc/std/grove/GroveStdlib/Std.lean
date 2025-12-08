/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import GroveStdlib.Std.CoreTypesAndOperations
import GroveStdlib.Std.LanguageConstructs
import GroveStdlib.Std.Libraries
import GroveStdlib.Std.OperatingSystemAbstractions

open Grove.Framework Widget

namespace GroveStdlib

namespace Std

def introduction : Node :=
  .text ⟨"introduction", "Welcome to the interactive Lean standard library outline!"⟩

end Std

def std : Node :=
  .section "stdlib" "The Lean standard library" #[
    Std.introduction,
    Std.coreTypesAndOperations,
    Std.languageConstructs,
    Std.libraries,
    Std.operatingSystemAbstractions
  ]

end GroveStdlib
