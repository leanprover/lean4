import Lean

open Lean Meta Elab Term Tactic

/-- Check if a goal is of a subsingleton type. -/
def Lean.MVarId.subsingleton? (g : MVarId) : MetaM Bool := do
  try
    _ ← Lean.Meta.synthInstance (← mkAppM `Subsingleton #[← g.getType])
    return true
  catch _ =>
    return false

/--
Check if a goal is "independent" of a list of other goals.
We say a goal is independent of other goals if assigning a value to it
can not change the solvability of the other goals.

This function only calculates a conservative approximation of this condition.
-/
def Lean.MVarId.independent? (L : List MVarId) (g : MVarId) : MetaM Bool := do
  let t ← instantiateMVars (← g.getType)
  if t.hasExprMVar then
    -- If the goal's type contains other meta-variables,
    -- we conservatively say that `g` is not independent.
    return false
  if t.isProp then
    -- If the goal is propositional,
    -- proof-irrelevance should ensure it is independent of any other goals.
    return true
  if ← g.subsingleton? then
    -- If the goal is a subsingleton, it should be independent of any other goals.
    return true
  -- Finally, we check if the goal `g` appears in the type of any of the goals `L`.
  let r ← L.allM fun g' => do
    let t' ← instantiateMVars (← g'.getType)
    pure <| !(← exprDependsOn' t' (.mvar g))
  return r

unsafe def evalTacticMUnsafe (stx : Syntax) : TermElabM (TacticM Unit) :=
  evalTerm (TacticM Unit) (mkApp (mkConst ``TacticM) (mkConst ``Unit)) stx

@[implemented_by evalTacticMUnsafe]
opaque evalTacticM (stx : Syntax) : TermElabM (TacticM Unit)

/-- The `run_tac doSeq` tactic executes code in `TacticM Unit`. -/
elab (name := runTac) "run_tac " e:doSeq : tactic => do
  ← evalTacticM (← `(discard do $e))

example : Σ α, Option α := by
  constructor
  -- Goals are `?fst : Type` and `?snd : Option ?fst`.
  -- Correctly, `independent?` claims neither is independent.
  -- (`?snd` because its type contains a metavariable, and `?fst` because `?snd`'s type depends on it)
  run_tac do
    let gs ← getGoals
    for g in gs do
      guard ! (← g.independent? gs)
  exact some 0

example : Σ α, Option α := by
  constructor
  -- Now we introduce a hypothesis in the second goal,
  -- thereby introducing a delayed assignment.
  rotate_left
  have := 0
  rotate_left
  -- Due to the issue in https://github.com/leanprover/lean4/issues/2483
  -- previously `independent?` incorrectly thought `?fst` was independent.
  run_tac do
    let gs ← getGoals
    for g in gs do
      guard ! (← g.independent? gs) <|> throwError m!"{← g.getType} was incorrectly considered independent!"
  exact some 0
