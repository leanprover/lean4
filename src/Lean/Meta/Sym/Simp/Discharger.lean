/-
Copyright (c) 2026 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Sym.Simp.SimpM
import Lean.Meta.AppBuilder
namespace Lean.Meta.Sym.Simp

abbrev Discharger := Expr → SimpM (Option Expr)

/-- Converts a `Simproc` into a discharger -/
def mkDischarger (p : Simproc) : Discharger := fun e => do
  match (← p e) with
  | .rfl _ => return none
  | .step e' h _ =>
    if e'.isTrue then
      return some <| mkOfEqTrueCore e h
    else
      return none

/-- Returns a discharger that uses the simplifier itself as the discharger. -/
def mkDefaultDischarger : Discharger :=
  mkDischarger simp

end Lean.Meta.Sym.Simp
