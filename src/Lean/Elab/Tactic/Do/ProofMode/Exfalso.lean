/-
Copyright (c) 2022 Lars König. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars König, Mario Carneiro, Sebastian Graf
-/
prelude
import Std.Tactic.Do.Syntax
import Lean.Elab.Tactic.Do.ProofMode.MGoal
import Lean.Elab.Tactic.Do.ProofMode.Basic

namespace Lean.Elab.Tactic.Do.ProofMode
open Std.Do
open Lean Elab Tactic Meta


-- set_option pp.all true in
-- #check ⌜False⌝
private def falseProp (σs : Expr) : Expr := -- ⌜False⌝ standing in for an empty conjunction of hypotheses
  mkApp3 (mkConst ``SVal.curry) (.sort .zero) σs <| mkLambda `escape .default (mkApp (mkConst ``SVal.StateTuple) σs) (mkConst ``False)

@[builtin_tactic Lean.Parser.Tactic.mexfalso]
def elabMExfalso : Tactic | _ => do
  let mvar ← getMainGoal
  mvar.withContext do
  let g ← instantiateMVars <| ← mvar.getType
  let some goal := parseMGoal? g | throwError "not in proof mode"
  let newGoal := { goal with target := falseProp goal.σs }
  let m ← mkFreshExprSyntheticOpaqueMVar newGoal.toExpr
  let prf := mkApp4 (mkConst ``SPred.exfalso) goal.σs goal.hyps goal.target m
  mvar.assign prf
  replaceMainGoal [m.mvarId!]
