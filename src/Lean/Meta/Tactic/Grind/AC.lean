/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Tactic.Grind.AC.Types
public import Lean.Meta.Tactic.Grind.AC.Util
public import Lean.Meta.Tactic.Grind.AC.Var
public import Lean.Meta.Tactic.Grind.AC.Internalize
public import Lean.Meta.Tactic.Grind.AC.Eq
public import Lean.Meta.Tactic.Grind.AC.Seq
public import Lean.Meta.Tactic.Grind.AC.Proof
public import Lean.Meta.Tactic.Grind.AC.DenoteExpr
public import Lean.Meta.Tactic.Grind.AC.ToExpr
public import Lean.Meta.Tactic.Grind.AC.VarRename
public import Lean.Meta.Tactic.Grind.AC.PP
public import Lean.Meta.Tactic.Grind.AC.Inv
public import Lean.Meta.Tactic.Grind.AC.Action
public section
namespace Lean.Meta.Grind.AC
builtin_initialize registerTraceClass `grind.ac
builtin_initialize registerTraceClass `grind.ac.assert
builtin_initialize registerTraceClass `grind.ac.internalize
builtin_initialize registerTraceClass `grind.ac.basis

builtin_initialize registerTraceClass `grind.debug.ac.op
builtin_initialize registerTraceClass `grind.debug.ac.simp
builtin_initialize registerTraceClass `grind.debug.ac.check
builtin_initialize registerTraceClass `grind.debug.ac.queue
builtin_initialize registerTraceClass `grind.debug.ac.superpose
builtin_initialize registerTraceClass `grind.debug.ac.eq

builtin_initialize
  acExt.setMethods
    (internalize := AC.internalize)
    (newEq       := AC.processNewEq)
    (newDiseq    := AC.processNewDiseq)
    (action      := Action.ac)
    (check       := AC.check')
    (checkInv    := AC.checkInvariants)

end Lean.Meta.Grind.AC
