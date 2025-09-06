/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Tactic.Grind.Arith.Linear.Types
public import Lean.Meta.Tactic.Grind.Arith.Linear.Util
public import Lean.Meta.Tactic.Grind.Arith.Linear.Var
public import Lean.Meta.Tactic.Grind.Arith.Linear.StructId
public import Lean.Meta.Tactic.Grind.Arith.Linear.IneqCnstr
public import Lean.Meta.Tactic.Grind.Arith.Linear.Reify
public import Lean.Meta.Tactic.Grind.Arith.Linear.DenoteExpr
public import Lean.Meta.Tactic.Grind.Arith.Linear.ToExpr
public import Lean.Meta.Tactic.Grind.Arith.Linear.Proof
public import Lean.Meta.Tactic.Grind.Arith.Linear.SearchM
public import Lean.Meta.Tactic.Grind.Arith.Linear.Search
public import Lean.Meta.Tactic.Grind.Arith.Linear.PropagateEq
public import Lean.Meta.Tactic.Grind.Arith.Linear.Internalize
public import Lean.Meta.Tactic.Grind.Arith.Linear.Model
public import Lean.Meta.Tactic.Grind.Arith.Linear.PP
public import Lean.Meta.Tactic.Grind.Arith.Linear.MBTC
public import Lean.Meta.Tactic.Grind.Arith.Linear.VarRename
public import Lean.Meta.Tactic.Grind.Arith.Linear.OfNatModule
public section
namespace Lean

builtin_initialize registerTraceClass `grind.linarith
builtin_initialize registerTraceClass `grind.linarith.internalize
builtin_initialize registerTraceClass `grind.linarith.assert
builtin_initialize registerTraceClass `grind.linarith.model
builtin_initialize registerTraceClass `grind.linarith.assert.unsat (inherited := true)
builtin_initialize registerTraceClass `grind.linarith.assert.trivial (inherited := true)
builtin_initialize registerTraceClass `grind.linarith.assert.store (inherited := true)
builtin_initialize registerTraceClass `grind.linarith.assert.ignored (inherited := true)

builtin_initialize registerTraceClass `grind.debug.linarith.search
builtin_initialize registerTraceClass `grind.debug.linarith.search.conflict (inherited := true)
builtin_initialize registerTraceClass `grind.debug.linarith.search.assign (inherited := true)
builtin_initialize registerTraceClass `grind.debug.linarith.search.split (inherited := true)
builtin_initialize registerTraceClass `grind.debug.linarith.search.backtrack (inherited := true)
builtin_initialize registerTraceClass `grind.debug.linarith.subst

end Lean
