/-
Copyright (c) 2026 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Tactic.Grind.Types
public import Lean.Meta.Tactic.Grind.Homo
public import Lean.Meta.Sym.Simp.SimpM
import Lean.Meta.Tactic.Grind.Diseq
import Lean.Meta.Sym.Simp.Rewrite
public section
namespace Lean.Meta.Grind.Homo

builtin_initialize registerTraceClass `grind.homo
builtin_initialize registerTraceClass `grind.homo.pred (inherited := true)

/-- Per-goal state for the `[grind homo]`/`[grind homo_pred]` solver extension. -/
structure State where
  /-- Persistent `Sym.simp` cache, reused across internalizations. -/
  cache : Sym.Simp.Cache := {}
  /-- Terms for which the `[grind homo_pred]` predicates have already been instantiated. -/
  processed : PHashSet ExprPtr := {}
  /-- Terms already visited by `markSourceTerm`. `Solvers.internalize` revisits terms,
  and re-marking a term whose class already has a solver term re-fires `newEq`; the
  visited set also avoids repeated `inferType` calls on revisits. -/
  visited : PHashSet ExprPtr := {}
  /-- `[grind homo]` rules, retrieved once per goal. -/
  thms? : Option Sym.Simp.Theorems := none
  /-- `[grind homo_pred]` predicates, retrieved once per goal. -/
  preds? : Option HomoPredTheorems := none
  /-- Head constants of the homomorphism source types, retrieved once per goal. -/
  sourceTypes? : Option NameSet := none

builtin_initialize stateExt : SolverExtension State ← registerSolverExtension (return {})

private def getThms : GoalM Sym.Simp.Theorems := do
  if let some thms := (← stateExt.getState).thms? then
    return thms
  let thms ← getHomoTheorems
  stateExt.modifyState fun s => { s with thms? := some thms }
  return thms

private def getPreds : GoalM HomoPredTheorems := do
  if let some preds := (← stateExt.getState).preds? then
    return preds
  let preds ← getHomoPredTheorems
  stateExt.modifyState fun s => { s with preds? := some preds }
  return preds

private def getSourceTypes : GoalM NameSet := do
  if let some tys := (← stateExt.getState).sourceTypes? then
    return tys
  let tys := (← getThms).homoSourceTypes
  stateExt.modifyState fun s => { s with sourceTypes? := some tys }
  return tys

/--
Marks `e` and its arguments as solver terms when their types are homomorphism source
types, so that the E-graph reports equalities and disequalities involving them to the
`processNewEq` and `processNewDiseq` hooks. Arguments must be marked here as well:
free variables are not internalized through the solver hooks, and become visible only
as arguments of internalized applications (e.g. `x` in `wu x`).
-/
private def markSourceTerm (e : Expr) : GoalM Unit := do
  let tys ← getSourceTypes
  if tys.isEmpty then return ()
  markIfSource tys e
  for arg in e.getAppArgs do
    markIfSource tys arg
where
  markIfSource (tys : NameSet) (e : Expr) : GoalM Unit := do
    if (← stateExt.getState).visited.contains { expr := e } then return ()
    stateExt.modifyState fun s => { s with visited := s.visited.insert { expr := e } }
    let τ ← inferType e
    let .const F _ := τ.getAppFn | return ()
    if tys.contains F then
      stateExt.markTerm e

/--
Rewriter for the `[grind homo]` rules with the stop condition: `grind` internalizes
terms bottom-up, so when no rule applies to a term that is already in the E-graph, the
term and all its subterms have already been processed by the engine, and there is
nothing to do at any depth. Traversal cost is thus proportional to the new terms
produced by the rewriting, not to the size of the input term.
-/
private def mkRewriter : GoalM Sym.Simp.Simproc := do
  let s ← get
  let rw := (← getThms).rewrite
  return fun e => do
    let r ← rw e
    if !r.isRfl then return r
    return .rfl (done := s.enodeMap.contains { expr := e })

/--
Applies the `[grind homo]` rules to `e` to fixpoint outside the E-graph.
Returns `some (e', h)` with `h : e = e'` if any rule was applied.
Intermediate terms do not enter the E-graph: only the final form is internalized by
the caller.
-/
private def applyHomo? (e : Expr) : GoalM (Option (Expr × Expr)) := do
  let rw ← mkRewriter
  let methods : Sym.Simp.Methods := { pre := rw, post := rw }
  let persistentCache := (← stateExt.getState).cache
  stateExt.modifyState fun s => { s with cache := {} }
  let (r, simpState) ← Sym.Simp.SimpM.run (Sym.Simp.simp e) (methods := methods)
    (s := { persistentCache })
  stateExt.modifyState fun s => { s with cache := simpState.persistentCache }
  let .step e' h _ _ := r | return none
  return some (e', h)

/--
Instantiates the `[grind homo_pred]` predicates triggered by `e` and asserts the
resulting facts. Each term is processed at most once per goal.
-/
private def firePreds (e : Expr) (generation : Nat) : GoalM Unit := do
  let .const declName _ := e.getAppFn | return ()
  unless (← getPreds).contains declName do return ()
  if (← stateExt.getState).processed.contains { expr := e } then return ()
  stateExt.modifyState fun s => { s with processed := s.processed.insert { expr := e } }
  for (proof, prop) in ← mkHomoPredInstances e do
    trace_goal[grind.homo.pred] "{prop}"
    addNewRawFact proof prop generation .input .other

/--
Internalization hook. Applies the `[grind homo]` rules to `e` to fixpoint; if a rule
applied, the final form is preprocessed, internalized, and merged with `e` in the
E-graph. Otherwise `e` is in homomorphism normal form, and the `[grind homo_pred]`
predicates are instantiated for it: rewriting has precedence over predicates, so
predicates fire only on normal forms.

Equality applications are skipped: equalities and disequalities are translated by the
`processNewEq` and `processNewDiseq` hooks, driven by the polarity the E-graph assigns
to them.
-/
def internalize (e : Expr) (_parent? : Option Expr) : GoalM Unit := do
  unless (← getConfig).homo do return ()
  unless e.isApp do return ()
  if e.isAppOf ``Eq then return ()
  markSourceTerm e
  let generation ← getGeneration e
  let some (e₁, h₁) ← applyHomo? e | firePreds e generation
  let r ← preprocess e₁
  let h ← mkEqTrans h₁ (← r.getProof)
  Grind.internalize r.expr generation
  trace_goal[grind.homo] "{e}\n===>\n{r.expr}"
  pushEq e r.expr h

/--
Equality hook: when the classes of `a` and `b` are merged and the `[grind homo]` set
translates `a = b`, asserts the translated (and fully reduced) equality. This is the
`=`-injection of the homomorphism: one fact per union, so a class with `n` elements
produces `n - 1` translated equalities; the transitive closure is handled by the
target-domain E-graph, and asserting `a = c` after `a = b` and `b = c` is a no-op
because no union takes place.
-/
def processNewEq (a b : Expr) : GoalM Unit := do
  unless (← getConfig).homo do return ()
  let eq ← shareCommon (← mkEq a b)
  let some (t, hEqProp) ← applyHomo? eq | return ()
  let fact ← mkEqMP hEqProp (← mkEqProof a b)
  let generation := max (← getGeneration a) (← getGeneration b)
  trace_goal[grind.homo] "{eq}\n===>\n{t}"
  addNewRawFact fact t generation .input .other

/--
Disequality hook: when `a ≠ b` is asserted and the `[grind homo]` set translates
`a = b`, asserts the negation of the translated equality. Unlike equalities,
disequalities are not propagated by congruence, and the target-domain solvers consume
them directly (e.g. `cutsat` case splits on `x ≠ 0`). The translation is justified by
the backward direction of the `=`-injection rule, i.e. the injectivity of the
homomorphism.
-/
def processNewDiseq (a b : Expr) : GoalM Unit := do
  unless (← getConfig).homo do return ()
  let eq ← shareCommon (← mkEq a b)
  let some (t, hEqProp) ← applyHomo? eq | return ()
  let hne ← mkDiseqProof a b
  let fact ← mkEqMP (← mkCongrArg (mkConst ``Not) hEqProp) hne
  let generation := max (← getGeneration a) (← getGeneration b)
  trace_goal[grind.homo] "{mkNot eq}\n===>\n{mkNot t}"
  addNewRawFact fact (mkNot t) generation .input .other

builtin_initialize
  stateExt.setMethods
    (internalize := Homo.internalize)
    (newEq       := Homo.processNewEq)
    (newDiseq    := Homo.processNewDiseq)

end Lean.Meta.Grind.Homo
