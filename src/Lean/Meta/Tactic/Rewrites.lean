/-
Copyright (c) 2023 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
prelude
import Lean.Meta.LazyDiscrTree
import Lean.Meta.Tactic.Assumption
import Lean.Meta.Tactic.Rewrite
import Lean.Meta.Tactic.Refl
import Lean.Meta.Tactic.SolveByElim
import Lean.Meta.Tactic.TryThis
import Lean.Util.Heartbeats

namespace Lean.Meta.Rewrites

open Lean.Meta.LazyDiscrTree (InitEntry MatchResult)
open Lean.Meta.SolveByElim

builtin_initialize registerTraceClass `Tactic.rewrites
builtin_initialize registerTraceClass `Tactic.rewrites.lemmas

/-- Extract the lemma, with arguments, that was used to produce a `RewriteResult`. -/
-- This assumes that `r.eqProof` was constructed as:
-- `mkApp6 (.const ``congrArg _) α eType lhs rhs motive heq`
-- in `Lean.Meta.Tactic.Rewrite` and we want `heq`.
def rewriteResultLemma (r : RewriteResult) : Option Expr :=
  if r.eqProof.isAppOfArity ``congrArg 6 then
    r.eqProof.getArg! 5
  else
    none

/-- Weight to multiply the "specificity" of a rewrite lemma by when rewriting forwards. -/
def forwardWeight := 2
/-- Weight to multiply the "specificity" of a rewrite lemma by when rewriting backwards. -/
def backwardWeight := 1

inductive RwDirection : Type where
  | forward : RwDirection
  | backward : RwDirection

private def addImport (name : Name) (constInfo : ConstantInfo) :
    MetaM (Array (InitEntry (Name × RwDirection))) := do
  if constInfo.isUnsafe then return #[]
  if !allowCompletion (←getEnv) name then return #[]
  -- We now remove some injectivity lemmas which are not useful to rewrite by.
  if name matches .str _ "injEq" then return #[]
  if name matches .str _ "sizeOf_spec" then return #[]
  match name with
  | .str _ n => if n.endsWith "_inj" ∨ n.endsWith "_inj'" then return #[]
  | _ => pure ()
  withNewMCtxDepth do withReducible do
    forallTelescopeReducing constInfo.type fun _ type => do
      match type.getAppFnArgs with
      | (``Eq, #[_, lhs, rhs])
      | (``Iff, #[lhs, rhs]) => do
        let a := Array.mkEmpty 2
        let a := a.push (← InitEntry.fromExpr lhs (name, RwDirection.forward))
        let a := a.push (← InitEntry.fromExpr rhs (name, RwDirection.backward))
        pure a
      | _ => return #[]

/-- Configuration for `DiscrTree`. -/
def discrTreeConfig : WhnfCoreConfig := {}

/-- Select `=` and `↔` local hypotheses. -/
def localHypotheses (except : List FVarId := []) : MetaM (Array (Expr × Bool × Nat)) := do
  let r ← getLocalHyps
  let mut result := #[]
  for h in r do
    if except.contains h.fvarId! then continue
    let (_, _, type) ← forallMetaTelescopeReducing (← inferType h)
    let type ← whnfR type
    match type.getAppFnArgs with
    | (``Eq, #[_, _, _])
    | (``Iff, #[_, _]) => do
      result := result.push (h, false, forwardWeight)
                    |>.push (h, true, backwardWeight)
    | _ => pure ()
  return result

/--
We drop `.star` and `Eq * * *` from the discriminator trees because
they match too much.
-/
def droppedKeys : List (List LazyDiscrTree.Key) := [[.star], [.const `Eq 3, .star, .star, .star]]

def createModuleTreeRef : MetaM (LazyDiscrTree.ModuleDiscrTreeRef (Name × RwDirection)) :=
  LazyDiscrTree.createModuleTreeRef addImport droppedKeys

private def ExtState := IO.Ref (Option (LazyDiscrTree (Name × RwDirection)))

private builtin_initialize ExtState.default : IO.Ref (Option (LazyDiscrTree (Name × RwDirection))) ← do
  IO.mkRef .none

private instance : Inhabited ExtState where
  default := ExtState.default

private builtin_initialize ext : EnvExtension ExtState ←
  registerEnvExtension (IO.mkRef .none)

/--
The maximum number of constants an individual task may perform.

The value was picked because it roughly corresponded to 50ms of work on the
machine this was developed on.  Smaller numbers did not seem to improve
performance when importing Std and larger numbers (<10k) seemed to degrade
initialization performance.
-/
private def constantsPerImportTask : Nat := 6500

def incPrio : Nat → Name × RwDirection → Name × Bool × Nat
| q, (nm, d) =>
  match d with
  | .forward => (nm, false, 2 * q)
  | .backward => (nm, true, q)

/-- Create function for finding relevant declarations. -/
def rwFindDecls (moduleRef : LazyDiscrTree.ModuleDiscrTreeRef (Name × RwDirection)) : Expr → MetaM (Array (Name × Bool × Nat)) :=
  LazyDiscrTree.findMatchesExt moduleRef ext addImport
      (droppedKeys := droppedKeys)
      (constantsPerTask := constantsPerImportTask)
      (adjustResult := incPrio)

/-- Data structure recording a potential rewrite to report from the `rw?` tactic. -/
structure RewriteResult where
  /-- The lemma we rewrote by.
  This is `Expr`, not just a `Name`, as it may be a local hypothesis. -/
  expr : Expr
  /-- `True` if we rewrote backwards (i.e. with `rw [← h]`). -/
  symm : Bool
  /-- The "weight" of the rewrite. This is calculated based on how specific the rewrite rule was. -/
  weight : Nat
  /-- The result from the `rw` tactic. -/
  result : Meta.RewriteResult
  /-- The metavariable context after the rewrite.
  This needs to be stored as part of the result so we can backtrack the state. -/
  mctx : MetavarContext
  rfl? : Bool

/-- Check to see if this expression (which must be a type) can be closed by `with_reducible rfl`. -/
def dischargableWithRfl? (mctx : MetavarContext) (e : Expr) : MetaM Bool := do
  try
    withoutModifyingState <| withMCtx mctx do
      -- We use `withReducible` here to follow the behaviour of `rw`.
      withReducible (← mkFreshExprMVar e).mvarId!.refl
      pure true
  catch _e =>
    pure false

/--
Pretty print the result of the rewrite.
-/
private def RewriteResult.ppResult (r : RewriteResult) : MetaM String :=
  return (← ppExpr r.result.eNew).pretty


/-- Should we try discharging side conditions? If so, using `assumption`, or `solve_by_elim`? -/
inductive SideConditions
| none
| assumption
| solveByElim

/-- Shortcut for calling `solveByElim`. -/
def solveByElim (goals : List MVarId) (depth : Nat := 6) : MetaM PUnit := do
  -- There is only a marginal decrease in performance for using the `symm` option for `solveByElim`.
  -- (measured via `lake build && time lake env lean test/librarySearch.lean`).
  let cfg : SolveByElimConfig := { maxDepth := depth, exfalso := false, symm := true }
  let ⟨lemmas, ctx⟩ ← mkAssumptionSet false false [] [] #[]
  let [] ← SolveByElim.solveByElim cfg lemmas ctx goals
    | failure

def rwLemma (ctx : MetavarContext) (goal : MVarId) (target : Expr) (side : SideConditions := .solveByElim)
    (lem : Expr ⊕ Name) (symm : Bool) (weight : Nat) : MetaM (Option RewriteResult) :=
  withMCtx ctx do
    let some expr ← (match lem with
    | .inl hyp => pure (some hyp)
    | .inr lem => some <$> mkConstWithFreshMVarLevels lem <|> pure none)
      | return none
    trace[Tactic.rewrites] m!"considering {if symm then "← " else ""}{expr}"
    let some result ← some <$> goal.rewrite target expr symm <|> pure none
      | return none
    if result.mvarIds.isEmpty then
      let mctx ← getMCtx
      let rfl? ← dischargableWithRfl? mctx result.eNew
      return some { expr, symm, weight, result, mctx, rfl? }
    else
      -- There are side conditions, which we try to discharge using local hypotheses.
      let discharge ←
        match side with
        | .none => pure false
        | .assumption => ((fun _ => true) <$> result.mvarIds.mapM fun m => m.assumption) <|> pure false
        | .solveByElim => (solveByElim result.mvarIds >>= fun _ => pure true) <|> pure false
      match discharge with
      | false =>
        return none
      | true =>
        -- If we succeed, we need to reconstruct the expression to report that we rewrote by.
        let some expr := rewriteResultLemma result | return none
        let expr ← instantiateMVars expr
        let (expr, symm) := if expr.isAppOfArity ``Eq.symm 4 then
            (expr.getArg! 3, true)
          else
            (expr, false)
        let mctx ← getMCtx
        let rfl? ← dischargableWithRfl? mctx result.eNew
        return some { expr, symm, weight, result, mctx, rfl? }

/--
Find keys which match the expression, or some subexpression.

Note that repeated subexpressions will be visited each time they appear,
making this operation potentially very expensive.
It would be good to solve this problem!

Implementation: we reverse the results from `getMatch`,
so that we return lemmas matching larger subexpressions first,
and amongst those we return more specific lemmas first.
-/
partial def getSubexpressionMatches (op : Expr → MetaM (Array α)) (e : Expr) : MetaM (Array α) := do
  match e with
  | .bvar _ => return #[]
  | .forallE _ _ _ _ =>
    forallTelescope e fun args body => do
      args.foldlM (fun acc arg => return acc ++ (← getSubexpressionMatches op (← inferType arg)))
        (← getSubexpressionMatches op body).reverse
  | .lam _ _ _ _
  | .letE _ _ _ _ _ =>
    lambdaLetTelescope e (fun args body => do
      args.foldlM (fun acc arg => return acc ++ (← getSubexpressionMatches op (← inferType arg)))
        (← getSubexpressionMatches op body).reverse)
  | _ =>
    let init := ((← op e).reverse)
    e.foldlM (init := init) (fun a f => return a ++ (← getSubexpressionMatches op f))

/--
Find lemmas which can rewrite the goal.

See also `rewrites` for a more convenient interface.
-/
def rewriteCandidates (hyps : Array (Expr × Bool × Nat))
    (moduleRef : LazyDiscrTree.ModuleDiscrTreeRef (Name × RwDirection))
    (target : Expr)
    (forbidden : NameSet := ∅) :
    MetaM (Array ((Expr ⊕ Name) × Bool × Nat)) := do
  -- Get all lemmas which could match some subexpression
  let candidates ← getSubexpressionMatches (rwFindDecls moduleRef) target
  -- Sort them by our preferring weighting
  -- (length of discriminant key, doubled for the forward implication)
  let candidates := candidates.insertionSort fun (_, _, rp) (_, _, sp) => rp > sp

  -- Now deduplicate. We can't use `Array.deduplicateSorted` as we haven't completely sorted,
  -- and in fact want to keep some of the residual ordering from the discrimination tree.
  let mut forward : NameSet := ∅
  let mut backward : NameSet := ∅
  let mut deduped := #[]
  for (l, s, w) in candidates do
    if forbidden.contains l then continue
    if s then
      if ¬ backward.contains l then
        deduped := deduped.push (l, s, w)
        backward := backward.insert l
    else
      if ¬ forward.contains l then
        deduped := deduped.push (l, s, w)
        forward := forward.insert l

  trace[Tactic.rewrites.lemmas] m!"Candidate rewrite lemmas:\n{deduped}"

  let hyps := hyps.map fun ⟨hyp, symm, weight⟩ => (Sum.inl hyp, symm, weight)
  let lemmas := deduped.map fun ⟨lem, symm, weight⟩ => (Sum.inr lem, symm, weight)
  pure <| hyps ++ lemmas

def RewriteResult.newGoal (r : RewriteResult) : Option Expr :=
  if r.rfl? = true then
    some (Expr.lit (.strVal "no goals"))
  else
    some r.result.eNew

def RewriteResult.addSuggestion (ref : Syntax) (r : RewriteResult) : Elab.TermElabM Unit := do
  withMCtx r.mctx do
    Tactic.TryThis.addRewriteSuggestion ref [(r.expr, r.symm)] (type? := r.newGoal) (origSpan? := ← getRef)

structure RewriteResultConfig where
  stopAtRfl : Bool
  max : Nat
  minHeartbeats : Nat
  goal : MVarId
  target : Expr
  side : SideConditions := .solveByElim
  mctx : MetavarContext

def takeListAux (cfg : RewriteResultConfig) (seen : Std.HashMap String Unit) (acc : Array RewriteResult)
    (xs : List ((Expr ⊕ Name) × Bool × Nat)) : MetaM (Array RewriteResult) := do
  let mut seen := seen
  let mut acc := acc
  for (lem, symm, weight) in xs do
    if (← getRemainingHeartbeats) < cfg.minHeartbeats then
      return acc
    if acc.size ≥ cfg.max then
      return acc
    let res ←
          withoutModifyingState <| withMCtx cfg.mctx do
            rwLemma cfg.mctx cfg.goal cfg.target cfg.side lem symm weight
    match res with
    | none => continue
    | some r =>
      let s ← withoutModifyingState <| withMCtx r.mctx r.ppResult
      if seen.contains s then
        continue
      let rfl? ← dischargableWithRfl? r.mctx r.result.eNew
      if cfg.stopAtRfl then
        if rfl? then
          return #[r]
        else
          seen := seen.insert s ()
          acc := acc.push r
      else
        seen := seen.insert s ()
        acc := acc.push r
  return acc

/-- Find lemmas which can rewrite the goal. -/
def findRewrites (hyps : Array (Expr × Bool × Nat))
    (moduleRef : LazyDiscrTree.ModuleDiscrTreeRef (Name × RwDirection))
    (goal : MVarId) (target : Expr)
    (forbidden : NameSet := ∅) (side : SideConditions := .solveByElim)
    (stopAtRfl : Bool) (max : Nat := 20)
    (leavePercentHeartbeats : Nat := 10) : MetaM (List RewriteResult) := do
  let mctx ← getMCtx
  let candidates ← rewriteCandidates hyps moduleRef target forbidden
  let minHeartbeats : Nat ←
        if (← getMaxHeartbeats) = 0 then
          pure 0
        else
          pure <| leavePercentHeartbeats * (← getRemainingHeartbeats) / 100
  let cfg : RewriteResultConfig :=
        { stopAtRfl, minHeartbeats, max, mctx, goal, target, side }
  return (← takeListAux cfg {} (Array.mkEmpty max) candidates.toList).toList

end Lean.Meta.Rewrites
