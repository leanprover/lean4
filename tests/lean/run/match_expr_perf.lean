/-
Copyright (c) 2023 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
prelude
import Lean.Elab.Tactic.Omega.Core
import Lean.Elab.Tactic.FalseOrByContra
import Lean.Meta.Tactic.Cases
import Lean.Elab.Tactic.Config

open Lean Meta Omega

set_option maxHeartbeats 5000
def pushNot (h P : Expr) : MetaM (Option Expr) := do
  let P ← whnfR P
  trace[omega] "pushing negation: {P}"
  match P with
  | .forallE _ t b _ =>
    if (← isProp t) && (← isProp b) then
     return some (mkApp4 (.const ``Decidable.and_not_of_not_imp []) t b
      (.app (.const ``Classical.propDecidable []) t) h)
    else
      return none
  | .app _ _ =>
    match_expr P with
    | LT.lt α _ x y => match_expr α with
      | Nat => return some (mkApp3 (.const ``Nat.le_of_not_lt []) x y h)
      | Int => return some (mkApp3 (.const ``Int.le_of_not_lt []) x y h)
      | Fin n => return some (mkApp4 (.const ``Fin.le_of_not_lt []) n x y h)
      | _ => return none
    | LE.le α _ x y => match_expr α with
      | Nat => return some (mkApp3 (.const ``Nat.lt_of_not_le []) x y h)
      | Int => return some (mkApp3 (.const ``Int.lt_of_not_le []) x y h)
      | Fin n => return some (mkApp4 (.const ``Fin.lt_of_not_le []) n x y h)
      | _ => return none
    | Eq α x y => match_expr α with
      | Nat => return some (mkApp3 (.const ``Nat.lt_or_gt_of_ne []) x y h)
      | Int => return some (mkApp3 (.const ``Int.lt_or_gt_of_ne []) x y h)
      | Fin n => return some (mkApp4 (.const ``Fin.lt_or_gt_of_ne []) n x y h)
      | _ => return none
    | Dvd.dvd α _ k x => match_expr α with
      | Nat => return some (mkApp3 (.const ``Nat.emod_pos_of_not_dvd []) k x h)
      | Int =>
        -- This introduces a disjunction that could be avoided by checking `k ≠ 0`.
        return some (mkApp3 (.const ``Int.emod_pos_of_not_dvd []) k x h)
      | _ => return none
    | Prod.Lex _ _ _ _ _ _ => return some (← mkAppM ``Prod.of_not_lex #[h])
    | Not P =>
      return some (mkApp3 (.const ``Decidable.of_not_not []) P
        (.app (.const ``Classical.propDecidable []) P) h)
    | And P Q =>
      return some (mkApp5 (.const ``Decidable.or_not_not_of_not_and []) P Q
        (.app (.const ``Classical.propDecidable []) P)
        (.app (.const ``Classical.propDecidable []) Q) h)
    | Or P Q =>
      return some (mkApp3 (.const ``and_not_not_of_not_or []) P Q h)
    | Iff P Q =>
      return some (mkApp5 (.const ``Decidable.and_not_or_not_and_of_not_iff []) P Q
        (.app (.const ``Classical.propDecidable []) P)
        (.app (.const ``Classical.propDecidable []) Q) h)
    | _ => return none
  | _ => return none
