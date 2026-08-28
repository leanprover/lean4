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

builtin_initialize registerTraceClass `grind.hom
builtin_initialize registerTraceClass `grind.hom.pred (inherited := true)

/-- Per-goal state for the `[grind hom]`/`[grind hom_pred]` solver extension. -/
structure State where
  /-- Persistent `Sym.simp` cache, reused across internalizations. -/
  cache : Sym.Simp.Cache := {}
  /-- Terms already visited during internalization. -/
  internalized : PHashSet ExprPtr := {}
  -- **Note**: Consider changing `mkInitial` to `CoreM`. Then, we can initialize the fields `thms`, `preds`, and `sourceTypes`
  -- at `mkInitial` and avoid this `initialized` flag.
  initialized : Bool := false
  /-- `[grind hom]` rules, retrieved once per goal. -/
  thms : Sym.Simp.Theorems := {}
  /-- `[grind hom_pred]` predicates, retrieved once per goal. -/
  preds : HomoPredTheorems := {}
  /-- Head constants of the homomorphism source types, retrieved once per goal. -/
  sourceTypes : NameSet := {}

builtin_initialize homExt : SolverExtension State ← registerSolverExtension (return {})

private def init : GoalM Unit := do
  if (← homExt.getState).initialized then
    return ()
  let thms ← getHomoTheorems
  let preds ← getHomoPredTheorems
  let sourceTypes ← getHomoSourceTypes
  homExt.modifyState fun s => { s with initialized := true, thms, preds, sourceTypes }

private def getThms : GoalM Sym.Simp.Theorems := do
  init
  return (← homExt.getState).thms

private def getPreds : GoalM HomoPredTheorems := do
  init
  return (← homExt.getState).preds

private def getSourceTypes : GoalM NameSet := do
  init
  return (← homExt.getState).sourceTypes

/--
Marks `e` when its type is a homomorphism source type, so that the core notifies this extension
of equalities and disequalities involving `e`.
-/
private def markSourceTerm (e : Expr) : GoalM Unit := do
  let tys ← getSourceTypes
  if tys.isEmpty then return ()
  let α ← Sym.inferType e
  let .const F _ := α.getAppFn | return ()
  if tys.contains F then
    homExt.markTerm e

/--
Instantiates the `[grind hom_pred]` predicates triggered by `e` and asserts the
resulting facts. Each term is processed at most once per goal.
-/
private def firePreds (e : Expr) (generation : Nat) : GoalM Unit := do
  let .const declName _ := e.getAppFn | return ()
  unless (← getPreds).contains declName do return ()
  for (proof, prop) in ← mkHomoPredInstances e do
    trace_goal[grind.hom.pred] "{prop}"
    addNewRawFact proof prop generation .input .other

/--
Rewriter for the `[grind hom]` rules with the stop condition: `grind` internalizes
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
Applies the `[grind hom]` rules to `e` to fixpoint outside the E-graph.
Returns `some (e', h)` with `h : e = e'` if any rule was applied.
Intermediate terms do not enter the E-graph: only the final form is internalized by
the caller.
-/
private def applyHomo? (e : Expr) : GoalM (Option (Expr × Expr)) := do
  let rw ← mkRewriter
  let methods : Sym.Simp.Methods := { pre := rw, post := rw }
  let persistentCache := (← homExt.getState).cache
  homExt.modifyState fun s => { s with cache := {} }
  let (r, simpState) ← Sym.Simp.SimpM.run (Sym.Simp.simp e) (methods := methods)
    (s := { persistentCache })
  homExt.modifyState fun s => { s with cache := simpState.persistentCache }
  let .step e' h _ _ := r | return none
  return some (e', h)

def internalize (e : Expr) (_parent? : Option Expr) : GoalM Unit := do
  unless (← getConfig).hom do return ()
  if e.isAppOf ``Eq then return () -- We do not internalize equalities
  -- Check whether term has already been internalized by this solver extension.
  if (← homExt.getState).internalized.contains { expr := e } then return ()
  homExt.modifyState fun s => { s with internalized := s.internalized.insert { expr := e } }
  markSourceTerm e
  let generation ← getGeneration e
  if let some (e₁, h₁) ← applyHomo? e then
    let r ← preprocess e₁
    let h ← mkEqTrans h₁ (← r.getProof)
    Grind.internalize r.expr generation
    trace_goal[grind.hom] "{e}\n===>\n{r.expr}"
    pushEq e r.expr h
  else
    firePreds e generation

/--
Equality hook: when the classes of `a` and `b` are merged and the `[grind hom]` set
translates `a = b`, asserts the translated (and fully reduced) equality. This is the
`=`-injection of the homomorphism: one fact per union, so a class with `n` elements
produces `n - 1` translated equalities; the transitive closure is handled by the
target-domain E-graph, and asserting `a = c` after `a = b` and `b = c` is a no-op
because no union takes place.
-/
def processNewEq (a b : Expr) : GoalM Unit := do
  unless (← getConfig).hom do return ()
  -- `a` and `b` may have different types when their classes were merged via `HEq`
  -- (e.g., `BitVec.cast` terms). The `=`-injection applies only to homogeneous equalities.
  unless (← hasSameType a b) do return ()
  let eq ← shareCommon (← mkEq a b)
  let some (t, hEqProp) ← applyHomo? eq | return ()
  let fact ← mkEqMP hEqProp (← mkEqProof a b)
  let generation := max (← getGeneration a) (← getGeneration b)
  trace_goal[grind.hom] "{eq}\n===>\n{t}"
  addNewRawFact fact t generation .input .other

/--
Disequality hook: when `a ≠ b` is asserted and the `[grind hom]` set translates
`a = b`, asserts the negation of the translated equality. Unlike equalities,
disequalities are not propagated by congruence, and the target-domain solvers consume
them directly (e.g. `cutsat` case splits on `x ≠ 0`). The translation is justified by
the backward direction of the `=`-injection rule, i.e. the injectivity of the
homomorphism.
-/
def processNewDiseq (a b : Expr) : GoalM Unit := do
  unless (← getConfig).hom do return ()
  -- See the same-type check at `processNewEq`.
  unless (← hasSameType a b) do return ()
  let eq ← shareCommon (← mkEq a b)
  let some (t, hEqProp) ← applyHomo? eq | return ()
  let hne ← mkDiseqProof a b
  let fact ← mkEqMP (← mkCongrArg (mkConst ``Not) hEqProp) hne
  let generation := max (← getGeneration a) (← getGeneration b)
  trace_goal[grind.hom] "{mkNot eq}\n===>\n{mkNot t}"
  addNewRawFact fact (mkNot t) generation .input .other

builtin_initialize
  homExt.setMethods
    (internalize := Homo.internalize)
    (newEq       := Homo.processNewEq)
    (newDiseq    := Homo.processNewDiseq)

end Lean.Meta.Grind.Homo
