/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Util.Trace
import Lean.Meta.Tactic.Grind.Arith.Cutsat.Types

namespace Lean

builtin_initialize registerTraceClass `grind.cutsat
builtin_initialize registerTraceClass `grind.cutsat.internalize
builtin_initialize registerTraceClass `grind.cutsat.internalize.term (inherited := true)

end Lean
