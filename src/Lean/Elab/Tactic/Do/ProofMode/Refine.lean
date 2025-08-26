/-
Copyright (c) 2022 Lars König. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars König, Mario Carneiro, Sebastian Graf
-/
module

prelude
public import Std.Tactic.Do.Syntax
public import Lean.Elab.Tactic.Do.ProofMode.Focus
public import Lean.Elab.Tactic.Do.ProofMode.Assumption
public import Lean.Elab.Tactic.Do.ProofMode.Exact

public section

namespace Lean.Elab.Tactic.Do.ProofMode
open Std.Do SPred.Tactic Lean.Parser.Tactic
open Lean Elab Tactic Meta

def patAsTerm (pat : MRefinePat) (expected : Option Expr := none) : OptionT TacticM Expr := do
  match pat with
  | .pure t => elabTerm t expected
  | .one name =>
    if let `(binderIdent| $name:ident) := name then
      elabTerm (← `($name)) expected
    else failure
  | _ => failure

partial def mRefineCore (goal : MGoal) (pat : MRefinePat) (k : MGoal → TSyntax ``binderIdent → TacticM Expr) : TacticM Expr := do
  match pat with
  | .stateful name => liftMetaM do
    match name with
    | `(binderIdent| $name:ident) => do
      let some prf ← goal.exact name | throwError "unknown hypothesis `{repr name}`"
      return prf
    | _ => do
      let some prf ← goal.assumption | throwError "could not solve {goal.target} by assumption"
      return prf
  | .pure t => do
    goal.exactPure t
  | .one name =>
      if let `(binderIdent| $_:ident) := name then
        mRefineCore goal (.pure ⟨name.raw⟩) k <|> mRefineCore goal (.stateful name) k
      else
        mRefineCore goal (.stateful name) k
  | .hole name => k goal name
  | .tuple [] => throwUnsupportedSyntax
  | .tuple [p] => mRefineCore goal p k
  | .tuple (p::ps) => do
    let T ← whnfR goal.target
    let f := T.getAppFn'
    let args := T.getAppArgs
    trace[Meta.debug] "f: {f}, args: {args}"
    if f.isConstOf ``SPred.and && args.size >= 3 then
      let T₁ := args[1]!.beta args[3...*]
      let T₂ := args[2]!.beta args[3...*]
      let prf₁ ← mRefineCore { goal with target := T₁ } p k
      let prf₂ ← mRefineCore { goal with target := T₂ } (.tuple ps) k
      return mkApp6 (mkConst ``SPred.and_intro [goal.u]) goal.σs goal.hyps T₁ T₂ prf₁ prf₂
    else if f.isConstOf ``SPred.exists && args.size >= 3 then
      let α := args[0]!
      let ψ := args[2]!
      let some witness ← patAsTerm p (some α) | throwError "pattern does not elaborate to a term to instantiate ψ"
      let prf ← mRefineCore { goal with target := ψ.beta (#[witness] ++ args[3...*]) } (.tuple ps) k
      let u ← getLevel α
      return mkApp6 (mkConst ``SPred.exists_intro' [u, goal.u]) α goal.σs goal.hyps ψ witness prf
    else throwError "Neither a conjunction nor an existential quantifier {T}"

@[builtin_tactic Lean.Parser.Tactic.mrefine]
def elabMRefine : Tactic
  | `(tactic| mrefine $pat:mrefinePat) => do
    let pat ← liftMacroM <| MRefinePat.parse pat
    let (mvar, goal) ← mStartMVar (← getMainGoal)
    mvar.withContext do

    let goals ← IO.mkRef #[]
    let prf ← mRefineCore goal pat fun goal name => do
      let m ← mkFreshExprSyntheticOpaqueMVar goal.toExpr name.raw.getId
      goals.modify (·.push m.mvarId!)
      return m
    mvar.assign prf
    replaceMainGoal (← goals.get).toList
  | _ => throwUnsupportedSyntax

@[builtin_tactic Lean.Parser.Tactic.mexists]
def elabMExists : Tactic
  | `(tactic| mexists $args,*) => do
    let pats ← args.getElems.mapM fun t => `(mrefinePat| ⌜$t⌝)
    let pat ← pats.foldrM (fun pat acc => `(mrefinePat| ⟨$pat, $acc⟩)) (← `(mrefinePat| ?_))
    evalTactic (← `(tactic| (mrefine $pat; try massumption)))
  | _ => throwUnsupportedSyntax
