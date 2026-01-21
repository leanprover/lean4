/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Sym.Pattern
import Lean.Util.CollectFVars
namespace Lean.Meta.Sym

/--
A rule for backward chaining (goal transformation).

Given a goal `... ⊢ T`, applying a `BackwardRule` derived from a theorem `∀ xs, P`
will unify `T` with `P`, assign the goal to the theorem application,
and return new goals for the unassigned arguments in `xs`.
-/
public structure BackwardRule where
  /-- The theorem used to create the rule. It is often of the form `Expr.const declName`. -/
  expr      : Expr
  /-- Precomputed pattern for efficient unification. -/
  pattern   : Pattern
  /--
  Indices of arguments that become new subgoals, ordered with
  non-dependent goals first. -/
  resultPos : List Nat


/--
Computes which argument positions become new subgoals after applying a backward rule.

Arguments are excluded from `resultPos` if:
- They appear in the conclusion (will be determined by unification)
- They are instance arguments (will be synthesized)

The result is ordered with non-dependent arguments first, then dependent ones.
This ordering is the same one used for the `MetaM` `apply` tactic.
It improves the user experience: non-dependent goals can be solved in
any order, while dependent goals are often resolved by solving the non-dependent ones first.
Example: `Exists.intro` produces two subgoal `?h : ?p ?w` and `?w : ?α`. The goal `?h` appears
first because solving it often solves `?w`.
-/
def mkResultPos (pattern : Pattern) : List Nat := Id.run do
  let auxPrefix := `_sym_pre
  -- Initialize "found" mask with arguments that can be synthesized by type class resolution.
  let mut found := pattern.isInstance
  let numArgs := pattern.varTypes.size
  let auxVars := pattern.varTypes.mapIdx fun i _ => mkFVar ⟨.num auxPrefix i⟩
  -- Collect arguments that occur in the pattern
  for fvarId in collectFVars {} (pattern.pattern.instantiateRev auxVars) |>.fvarIds do
    let .num pre idx := fvarId.name | pure ()
    if pre == auxPrefix then
      found := found.set! idx true
  let argTypes := pattern.varTypes.mapIdx fun i type => type.instantiateRevRange 0 i auxVars
  -- Collect dependent and non-dependent arguments that become new goals
  -- An argument is considered dependent only if there is another goal whose type depends on it.
  let mut deps := #[]
  let mut nonDeps := #[]
  for i in *...numArgs do
    unless found[i]! do
      let auxVar := auxVars[i]!
      let mut isDep := false
      for j in (i+1)...numArgs do
        unless found[j]! do
          let argType := argTypes[j]!
          if argType.containsFVar auxVar.fvarId! then
            isDep := true
            break
      if isDep then
        deps := deps.push i
      else
        nonDeps := nonDeps.push i
  return (nonDeps ++ deps).toList

/--
Creates a `BackwardRule` from a declaration name.

The `num?` parameter optionally limits how many arguments are included in the pattern
(useful for partially applying theorems).
-/
public def mkBackwardRuleFromDecl (declName : Name) (num? : Option Nat := none) : MetaM BackwardRule := do
  let pattern ← mkPatternFromDecl declName num?
  let resultPos := mkResultPos pattern
  return { expr := mkConst declName, pattern, resultPos }

/--
Creates a value to assign to input goal metavariable using unification result.

Handles both constant expressions (common case, avoids `instantiateLevelParams`)
and general expressions.
-/
def mkValue (expr : Expr) (pattern : Pattern) (result : MatchUnifyResult) : Expr :=
  if let .const declName [] := expr then
    mkAppN (mkConst declName result.us) result.args
  else
    mkAppN (expr.instantiateLevelParams pattern.levelParams result.us) result.args

/--
Applies a backward rule to a goal, returning new subgoals.

1. Unifies the goal type with the rule's pattern
2. Assigns the goal metavariable to the theorem application
3. Returns new goals for unassigned arguments (per `resultPos`)

Returns `none` if unification fails.
-/
public def BackwardRule.apply? (mvarId : MVarId) (rule : BackwardRule) : SymM (Option (List MVarId)) := mvarId.withContext do
  let decl ← mvarId.getDecl
  if let some result ← rule.pattern.unify? decl.type then
    mvarId.assign (mkValue rule.expr rule.pattern result)
    return some <| rule.resultPos.map fun i =>
      result.args[i]!.mvarId!
  else
    return none

/--
Similar to `BackwardRule.apply?`, but throws an error if unification fails.
-/
public def BackwardRule.apply (mvarId : MVarId) (rule : BackwardRule) : SymM (List MVarId) := mvarId.withContext do
  let decl ← mvarId.getDecl
  if let some result ← rule.pattern.unify? decl.type then
    mvarId.assign (mkValue rule.expr rule.pattern result)
    return rule.resultPos.map fun i =>
      result.args[i]!.mvarId!
  else
    throwError "rule is not applicable to goal{mvarId}rule:{indentExpr rule.expr}"

end Lean.Meta.Sym
