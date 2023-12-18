/-
Copyright (c) 2023 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Meta.Tactic.SymEval.Types
import Lean.Meta.Tactic.SymEval.Main

namespace Lean

builtin_initialize registerTraceClass `Meta.Tactic.seval
builtin_initialize registerTraceClass `Meta.Tactic.seval.visit

end Lean
