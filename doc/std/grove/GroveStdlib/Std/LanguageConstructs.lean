/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Grove.Framework
import GroveStdlib.Std.LanguageConstructs.ComparisonOrderingHashing
import GroveStdlib.Std.LanguageConstructs.Monads
import GroveStdlib.Std.LanguageConstructs.RangesAndIterators

open Grove.Framework Widget

namespace GroveStdlib.Std

namespace LanguageConstructs

end LanguageConstructs

def languageConstructs : Node :=
  .section "language-constructs" "Language constructs" #[
    LanguageConstructs.comparisonOrderingHashing,
    LanguageConstructs.monads,
    LanguageConstructs.rangesAndIterators
  ]

end GroveStdlib.Std
