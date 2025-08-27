/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Tactic.Grind.AC.Util
public section
namespace Lean.Meta.Grind.AC
/-- For each structure `s` s.t. `a` and `b` are elements of, execute `k` -/
@[specialize] def withExprs (a b : Expr) (k : ACM Unit) : GoalM Unit := do
  let ids₁ ← getTermOpIds a
  if ids₁.isEmpty then return ()
  let ids₂ ← getTermOpIds b
  go ids₁ ids₂
where
  go : List Nat → List Nat → GoalM Unit
    | [], _ => return ()
    | _, [] => return ()
    | id₁::ids₁, id₂::ids₂ => do
      if id₁ == id₂ then
        ACM.run id₁ k; go ids₁ ids₂
      else if id₁ < id₂ then
        go ids₁ (id₂::ids₂)
      else
        go (id₁::ids₁) ids₂

@[export lean_process_ac_eq]
def processNewEqImpl (a b : Expr) : GoalM Unit := withExprs a b do
  trace[grind.ac.assert] "{a} = {b}"
  -- TODO

@[export lean_process_ac_diseq]
def processNewDiseqImpl (a b : Expr) : GoalM Unit := withExprs a b do
  trace[grind.ac.assert] "{a} ≠ {b}"
  -- TODO

end Lean.Meta.Grind.AC
