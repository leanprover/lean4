/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Meta.Tactic.Grind.Attr
import Lean.Meta.Tactic.Grind.RevertAll
import Lean.Meta.Tactic.Grind.Types
import Lean.Meta.Tactic.Grind.Preprocessor
import Lean.Meta.Tactic.Grind.Util
import Lean.Meta.Tactic.Grind.Cases
import Lean.Meta.Tactic.Grind.Injection
import Lean.Meta.Tactic.Grind.Core
import Lean.Meta.Tactic.Grind.Canon
import Lean.Meta.Tactic.Grind.MarkNestedProofs

namespace Lean

builtin_initialize registerTraceClass `grind
builtin_initialize registerTraceClass `grind.eq
builtin_initialize registerTraceClass `grind.issues
builtin_initialize registerTraceClass `grind.add
builtin_initialize registerTraceClass `grind.pre
builtin_initialize registerTraceClass `grind.debug

end Lean
