/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Grove.Framework
import GroveStdlib.Std.CoreTypesAndOperations.BasicTypes
import GroveStdlib.Std.CoreTypesAndOperations.Containers
import GroveStdlib.Std.CoreTypesAndOperations.Numbers
import GroveStdlib.Std.CoreTypesAndOperations.StringsAndFormatting

open Grove.Framework Widget

namespace GroveStdlib.Std

namespace CoreTypesAndOperations

end CoreTypesAndOperations

def coreTypesAndOperations : Node :=
  .section "core-types-and-operations" "Core types and operations" #[
    CoreTypesAndOperations.basicTypes,
    CoreTypesAndOperations.containers,
    CoreTypesAndOperations.numbers,
    CoreTypesAndOperations.stringsAndFormatting
  ]

end GroveStdlib.Std
