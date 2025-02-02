/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Meta.Tactic.Try.Collect

namespace Lean

builtin_initialize registerTraceClass `try
builtin_initialize registerTraceClass `try.collect
builtin_initialize registerTraceClass `try.collect.funInd

builtin_initialize registerTraceClass `try.debug.funInd

end Lean
