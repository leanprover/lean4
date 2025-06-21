/-
Copyright (c) 2022 Lars König. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars König, Mario Carneiro, Sebastian Graf
-/
prelude
import Std.Tactic.Do.Syntax
import Lean.Elab.Tactic.Do.ProofMode.Focus
import Lean.Elab.Tactic.Do.ProofMode.Assumption
import Lean.Elab.Tactic.Do.ProofMode.Exact

namespace Lean.Elab.Tactic.Do.ProofMode
open Std.Do Lean.Parser.Tactic
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
      let some prf ← goal.exact name | throwError "unknown hypothesis '{repr name}'"
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
    if let some (σs, T₁, T₂) := parseAnd? T.consumeMData then
      let prf₁ ← mRefineCore { goal with target := T₁ } p k
      let prf₂ ← mRefineCore { goal with target := T₂ } (.tuple ps) k
      return mkApp6 (mkConst ``SPred.and_intro) σs goal.hyps T₁ T₂ prf₁ prf₂
    else if let some (α, σs, ψ) := T.app3? ``SPred.exists then
      let some witness ← patAsTerm p (some α) | throwError "pattern does not elaborate to a term to instantiate ψ"
      let prf ← mRefineCore { goal with target := ψ.betaRev #[witness] } (.tuple ps) k
      let u ← getLevel α
      return mkApp6 (mkConst ``SPred.exists_intro' [u]) α σs goal.hyps ψ witness prf
    else throwError "Neither a conjunction nor an existential quantifier {goal.target}"

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

macro_rules
  | `(tactic| mexists $args,*) => do
  let pats ← args.getElems.mapM fun t => `(mrefinePat| ⌜$t⌝)
  let pat ← pats.foldrM (fun pat acc => `(mrefinePat| ⟨$pat, $acc⟩)) (← `(mrefinePat| ?_))
  `(tactic| (mrefine $pat; try massumption))
