/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Sym.Pattern
import Lean.Util.FindMVar
import Init.Data.Range.Polymorphic.Iterators
namespace Lean.Meta.Sym

/--
A rule for backward chaining (goal transformation).

Given a goal `... ⊢ T`, applying a `BackwardRule` derived from a theorem `∀ xs, P`
will unify `T` with `P`, assign the goal to the theorem application,
and return argument metavariables as new goals, some of which may already be assigned.
-/
public structure BackwardRule where
  /-- The theorem used to create the rule. It is often of the form `Expr.const declName`. -/
  expr      : Expr
  /-- Precomputed pattern for efficient unification. -/
  pattern   : Pattern
  /--
  Indices of arguments that may become new subgoals, ordered with
  non-dependent goals first. -/
  resultPos : List Nat

/--
Marks argument variables whose occurrences are examined by pattern matching.

Syntactic variable collection is insufficient because proof irrelevance lets the matcher skip
proof arguments. Variables occurring only inside these proofs may remain unassigned even when
no old metavariables are assigned, so `mkResultPos` must retain them as potential goals.

For example:
```lean
opaque proofArg : True → Nat
def Wrapped (p : Prop) : Prop := p
theorem r {β : Type} (h : β → True) :
    Wrapped (∀ x : β, proofArg (h x) = proofArg (h x)) := fun _ => rfl
```
Matching the conclusion against
`Wrapped (∀ _ : Nat, proofArg True.intro = proofArg True.intro)` determines `β := Nat` but skips
the proof arguments `h x`. We leave `h` unmarked so it becomes a goal.

Bare proof variables outside binders are still marked because phase 1 binds them directly.
Proof arguments under binders are skipped conservatively; their variables may be assigned later,
which is allowed for returned goals.
-/
partial def markMatchedVars (pattern : Pattern) (e : Expr) (offset : Nat)
    (found : Array Bool) : Array Bool := Id.run do
  unless e.hasLooseBVars do return found
  match e with
  | .bvar idx =>
    return if idx ≥ offset then found.set! (found.size - (idx - offset) - 1) true else found
  | .app .. =>
    let f := e.getAppFn
    let args := e.getAppArgs
    let info? := f.constName?.bind pattern.fnInfos.find?
    let mut found := markMatchedVars pattern f offset found
    for i in *...args.size do
      if let some info := info? then
        if let some argInfo := info.argsInfo[i]? then
          if argInfo.isProof && !(offset == 0 && args[i]!.isBVar) then
            continue
      found := markMatchedVars pattern args[i]! offset found
    return found
  | .forallE _ d b _ | .lam _ d b _ =>
    return markMatchedVars pattern b (offset + 1) (markMatchedVars pattern d offset found)
  | .mdata _ b => return markMatchedVars pattern b offset found
  | .letE .. | .proj .. => unreachable!
  | _ => return found


/--
Computes which argument positions become new subgoals after applying a backward rule.

Arguments are excluded from `resultPos` if:
- They have an occurrence examined by matching the conclusion
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
  let numArgs := pattern.varTypes.size
  let found := if let some varInfos := pattern.varInfos? then
     varInfos.argsInfo.map fun info : ProofInstArgInfo => info.isInstance
  else
     Array.replicate numArgs false
  let auxVars := pattern.varTypes.mapIdx fun i _ => mkFVar ⟨.num auxPrefix i⟩
  let found := markMatchedVars pattern pattern.pattern 0 found
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
Creates a `BackwardRule` from an expression.

`levelParams` is not `[]` if the expression is supposed to be
universe polymorphic.

The `num?` parameter optionally limits how many arguments are included in the pattern
(useful for partially applying theorems).
-/
public def mkBackwardRuleFromExpr (e : Expr) (levelParams : List Name := []) (num? : Option Nat := none) : MetaM BackwardRule := do
  let pattern ← mkPatternFromExpr e levelParams num?
  let resultPos := mkResultPos pattern
  let e := e.instantiateLevelParams levelParams (pattern.levelParams.map mkLevelParam)
  return { expr := e, pattern, resultPos }

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

public inductive ApplyResult where
  | failed
  | goals (mvarIds : List MVarId)

/-- Returns an unassigned argument metavariable created by this application. -/
def getNewGoal? (arg : Expr) (mvarCounter : Nat) : MetaM (Option MVarId) := do
  let .mvar mvarId := arg | return none
  if (← mvarId.isAssigned) || (← mvarId.getDecl).index < mvarCounter then return none
  return some mvarId

/-- Recovers argument goals not determined by unification, placing non-dependent goals first. -/
def collectNewGoals (args : Array Expr) (mvarCounter : Nat) : SymM (List MVarId) := do
  let mvarIds ← args.filterMapM (getNewGoal? · mvarCounter)
  let types ← mvarIds.mapM fun mvarId => return (← mvarId.getDecl).type
  let mut nonDeps := #[]
  let mut deps := #[]
  for mvarId in mvarIds do
    if types.any (fun type => (type.findMVar? (· == mvarId)).isSome) then
      deps := deps.push mvarId
    else
      nonDeps := nonDeps.push mvarId
  return (nonDeps ++ deps).toList

/--
Applies a backward rule to a goal, returning new subgoals.

1. Unifies the goal type with the rule's pattern
2. Assigns the goal metavariable to the theorem application
3. Returns argument metavariables as new goals, possibly including assigned ones

Returns `.failed` if unification fails, or if an instance argument could not be synthesized.
When returning `.failed`, the metavariable context is restored.
-/
public def BackwardRule.apply (mvarId : MVarId) (rule : BackwardRule) : SymM ApplyResult := mvarId.withContext do
  let decl ← mvarId.getDecl
  let mctx ← getMCtx
  if let some result ← rule.pattern.unify? decl.type then
    -- `mkResultPos` omits instance arguments from `resultPos`, assuming type class resolution
    -- discharges them. An instance that could not be resolved is not a subgoal, so assigning the
    -- goal anyway would leave a loose instance metavariable in the proof term (surfacing later as a
    -- kernel unresolved-metavariable error). Report the rule as inapplicable instead.
    if result.unresolvedInsts.isEmpty then
      mvarId.assign (mkValue rule.expr rule.pattern result)
      -- Assigning a target metavariable can leave conclusion arguments undetermined.
      if result.assignedOld then
        return .goals (← collectNewGoals result.args mctx.mvarCounter)
      else
        return .goals <| rule.resultPos.map fun i =>
          result.args[i]!.mvarId!
  -- Undo the assignments made by `unify?`.
  setMCtx mctx
  return .failed

/--
Similar to `BackwardRule.apply', but throws an error if unification fails.
-/
public def BackwardRule.apply' (mvarId : MVarId) (rule : BackwardRule) : SymM (List MVarId) := do
  let .goals mvarIds ← rule.apply mvarId
    | throwError "rule is not applicable to goal{mvarId}rule:{indentExpr rule.expr}"
  return mvarIds

end Lean.Meta.Sym
