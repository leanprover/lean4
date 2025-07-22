/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
public import Lean.Meta.Tactic.Grind.Arith.Offset.Main
public import Lean.Meta.Tactic.Grind.Arith.Offset.Proof
public import Lean.Meta.Tactic.Grind.Arith.Offset.Util
public import Lean.Meta.Tactic.Grind.Arith.Offset.Types

public section

namespace Lean

builtin_initialize registerTraceClass `grind.offset
builtin_initialize registerTraceClass `grind.offset.dist
builtin_initialize registerTraceClass `grind.offset.internalize
builtin_initialize registerTraceClass `grind.offset.internalize.term (inherited := true)
builtin_initialize registerTraceClass `grind.offset.propagate
builtin_initialize registerTraceClass `grind.offset.eq
builtin_initialize registerTraceClass `grind.offset.eq.to (inherited := true)
builtin_initialize registerTraceClass `grind.offset.eq.from (inherited := true)
builtin_initialize registerTraceClass `grind.offset.model

builtin_initialize registerTraceClass `grind.debug.offset
builtin_initialize registerTraceClass `grind.debug.offset.proof

end Lean
