/-
Copyright (c) 2021 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, David Renshaw
-/
prelude
import Lean.Meta.Tactic.SolveByElim
import Lean.Elab.Tactic.Config

namespace Lean.Elab.Tactic.SolveByElim
open Meta

open Lean.Parser.Tactic
open Lean.Parser.Tactic.SolveByElim

open Lean.Meta.SolveByElim (SolveByElimConfig mkAssumptionSet)

/--
Allow elaboration of `Config` arguments to tactics.
-/
declare_config_elab elabConfig Lean.Meta.SolveByElim.SolveByElimConfig

/--
Allow elaboration of `ApplyRulesConfig` arguments to tactics.
-/
declare_config_elab elabApplyRulesConfig Lean.Meta.SolveByElim.ApplyRulesConfig

/--
Parse the lemma argument of a call to `solve_by_elim`.
The first component should be true if `*` appears at least once.
The second component should contain each term `t`in the arguments.
The third component should contain `t` for each `-t` in the arguments.
-/
def parseArgs (s : Option (TSyntax ``args)) :
    Bool × List Term × List Term :=
  let args : Array (TSyntax ``arg) := match s with
  | some s => match s with
    | `(args| [$args,*]) => args.getElems
    | _ => #[]
  | none => #[]
  let args : Array (Option (Term ⊕ Term)) := args.map fun t => match t with
    | `(arg| $_:star) => none
    | `(arg| - $t:term) => some (Sum.inr t)
    | `(arg| $t:term) => some (Sum.inl t)
    | _ => panic! "Unreachable parse of solve_by_elim arguments."
  let args := args.toList
  (args.contains none,
    args.filterMap fun o => o.bind Sum.getLeft?,
    args.filterMap fun o => o.bind Sum.getRight?)

/-- Parse the `using ...` argument for `solve_by_elim`. -/
def parseUsing (s : Option (TSyntax ``using_)) : Array Ident :=
  match s with
  | some s => match s with
    | `(using_ | using $ids,*) => ids.getElems
    | _ => #[]
  | none => #[]

/-- Wrapper for `solveByElim` that processes a list of `Term`s
that specify the lemmas to use. -/
def processSyntax (cfg : SolveByElimConfig := {}) (only star : Bool) (add remove : List Term)
    (use : Array Ident) (goals : List MVarId) : MetaM (List MVarId) := do
  if !remove.isEmpty && goals.length > 1 then
    throwError "Removing local hypotheses is not supported when operating on multiple goals."
  let ⟨lemmas, ctx⟩ ← mkAssumptionSet only star add remove use
  SolveByElim.solveByElim cfg lemmas ctx goals

@[builtin_tactic Lean.Parser.Tactic.applyAssumption]
def evalApplyAssumption : Tactic := fun stx =>
  match stx with
  | `(tactic| apply_assumption $[$cfg]? $[only%$o]? $[$t:args]? $[$use:using_]?) => do
    let (star, add, remove) := parseArgs t
    let use := parseUsing use
    let cfg ← elabConfig (mkOptionalNode cfg)
    let cfg := { cfg with
      backtracking := false
      maxDepth := 1 }
    replaceMainGoal (← processSyntax cfg o.isSome star add remove use [← getMainGoal])
  | _ => throwUnsupportedSyntax

/--
Elaborator for apply_rules.

See `Lean.MVarId.applyRules` for a `MetaM` level analogue of this tactic.
-/
@[builtin_tactic Lean.Parser.Tactic.applyRules]
def evalApplyRules : Tactic := fun stx =>
  match stx with
  | `(tactic| apply_rules $[$cfg]? $[only%$o]? $[$t:args]? $[$use:using_]?) => do
    let (star, add, remove) := parseArgs t
    let use := parseUsing use
    let cfg ← elabApplyRulesConfig (mkOptionalNode cfg)
    let cfg := { cfg with backtracking := false }
    liftMetaTactic fun g => processSyntax cfg o.isSome star add remove use [g]
  | _ => throwUnsupportedSyntax

@[builtin_tactic Lean.Parser.Tactic.solveByElim]
def evalSolveByElim : Tactic := fun stx =>
  match stx with
  | `(tactic| solve_by_elim $[*%$s]? $[$cfg]? $[only%$o]? $[$t:args]? $[$use:using_]?) => do
    let (star, add, remove) := parseArgs t
    let use := parseUsing use
    let goals ← if s.isSome then
      getGoals
    else
      pure [← getMainGoal]
    let cfg ← elabConfig (mkOptionalNode cfg)
    let [] ← processSyntax cfg o.isSome star add remove use goals |
      throwError "solve_by_elim unexpectedly returned subgoals"
    pure ()
  | _ => throwUnsupportedSyntax

end Lean.Elab.Tactic.SolveByElim
