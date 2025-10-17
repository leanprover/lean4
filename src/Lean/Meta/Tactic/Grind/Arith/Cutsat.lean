/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Tactic.Grind.Arith.Cutsat.DvdCnstr
public import Lean.Meta.Tactic.Grind.Arith.Cutsat.LeCnstr
public import Lean.Meta.Tactic.Grind.Arith.Cutsat.Search
public import Lean.Meta.Tactic.Grind.Arith.Cutsat.Inv
public import Lean.Meta.Tactic.Grind.Arith.Cutsat.Proof
public import Lean.Meta.Tactic.Grind.Arith.Cutsat.Types
public import Lean.Meta.Tactic.Grind.Arith.Cutsat.Util
public import Lean.Meta.Tactic.Grind.Arith.Cutsat.Var
public import Lean.Meta.Tactic.Grind.Arith.Cutsat.EqCnstr
public import Lean.Meta.Tactic.Grind.Arith.Cutsat.SearchM
public import Lean.Meta.Tactic.Grind.Arith.Cutsat.Model
public import Lean.Meta.Tactic.Grind.Arith.Cutsat.MBTC
public import Lean.Meta.Tactic.Grind.Arith.Cutsat.Nat
public import Lean.Meta.Tactic.Grind.Arith.Cutsat.CommRing
public import Lean.Meta.Tactic.Grind.Arith.Cutsat.VarRename
public import Lean.Meta.Tactic.Grind.Arith.Cutsat.Action
public section
namespace Lean.Meta.Grind.Arith.Cutsat
builtin_initialize registerTraceClass `grind.cutsat
builtin_initialize registerTraceClass `grind.cutsat.nonlinear
builtin_initialize registerTraceClass `grind.cutsat.model
builtin_initialize registerTraceClass `grind.cutsat.assert
builtin_initialize registerTraceClass `grind.cutsat.assert.trivial
builtin_initialize registerTraceClass `grind.cutsat.assert.unsat
builtin_initialize registerTraceClass `grind.cutsat.assert.store
builtin_initialize registerTraceClass `grind.cutsat.assert.nonlinear

builtin_initialize registerTraceClass `grind.debug.cutsat.subst
builtin_initialize registerTraceClass `grind.debug.cutsat.search
builtin_initialize registerTraceClass `grind.debug.cutsat.search.split (inherited := true)
builtin_initialize registerTraceClass `grind.debug.cutsat.search.assign (inherited := true)
builtin_initialize registerTraceClass `grind.debug.cutsat.search.conflict (inherited := true)
builtin_initialize registerTraceClass `grind.debug.cutsat.search.backtrack (inherited := true)
builtin_initialize registerTraceClass `grind.debug.cutsat.internalize
builtin_initialize registerTraceClass `grind.debug.cutsat.toInt
builtin_initialize registerTraceClass `grind.debug.cutsat.search.cnstrs
builtin_initialize registerTraceClass `grind.debug.cutsat.search.reorder
builtin_initialize registerTraceClass `grind.debug.cutsat.elimEq

builtin_initialize
  cutsatExt.setMethods
    (internalize := Cutsat.internalize)
    (newEq       := Cutsat.processNewEq)
    (newDiseq    := Cutsat.processNewDiseq)
    (check       := Cutsat.check)
    (checkInv    := Cutsat.checkInvariants)
    (mbtc        := Cutsat.mbtc)
    (mkTactic?   := return some (← `(grind| lia)))

end Lean.Meta.Grind.Arith.Cutsat
