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
import Init.Grind.Homo.Extra
import Lean.Meta.NatInstTesters
import Lean.Meta.Sym.LitValues
import Lean.Meta.Tactic.Grind.Diseq
import Lean.Meta.Sym.Simp.Rewrite
import Lean.Meta.Sym.Simp.EvalGround
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
Decomposes a mask `c` of the form `1…10…0` (at least one `1`) into `(n, k)` with
`c = (2^n - 1) * 2^k`.
-/
private def maskOnesZeros? (c : Nat) : Option (Nat × Nat) := do
  guard (c != 0)
  -- `c ^^^ (c - 1)` is `2^(k+1) - 1` where `k` is the number of trailing zeros of `c`.
  let k := (c ^^^ (c - 1)).log2
  let c := c >>> k
  let n := c.log2 + 1
  guard (c + 1 == 1 <<< n)
  return (n, k)

private def mkNatDiv (a b : Expr) : Expr :=
  mkApp6 (mkConst ``HDiv.hDiv [0, 0, 0]) Nat.mkType Nat.mkType Nat.mkType Nat.mkInstHDiv a b

private def mkNatMod (a b : Expr) : Expr :=
  mkApp6 (mkConst ``HMod.hMod [0, 0, 0]) Nat.mkType Nat.mkType Nat.mkType Nat.mkInstHMod a b

private def mkNatEqRefl (a : Expr) : Expr :=
  mkApp2 (mkConst ``Eq.refl [1]) Nat.mkType a

/--
Rewrites `x &&& c` and `c &&& x` over `Nat`, where `c` is a literal mask of the form
`1…10…0`, i.e. `c = (2^n - 1) * 2^k`, into `x % 2^n` when `k = 0` and into
`x / 2^k % 2^n * 2^k` otherwise, with the powers evaluated to literals. `cutsat`
supports `%`, `/`, and `*` by literals, but not `&&&`. The side conditions of the
theorems in `Init.Grind.Homo.Extra` are ground equalities between literals and
closed arithmetic terms, discharged by `rfl`.
-/
private def andMaskSimproc : Sym.Simp.Simproc := fun e => do
  let_expr HAnd.hAnd α _ _ inst a b := e | return .rfl
  unless α.isConstOf ``Nat do return .rfl
  unless (← Structural.isInstHAndNat inst) do return .rfl
  let (x, c, cVal, flipped) ←
    if let some cVal := (Sym.getNatValue? b).run then pure (a, b, cVal, false)
    else if let some cVal := (Sym.getNatValue? a).run then pure (b, a, cVal, true)
    else return .rfl
  let some (n, k) := maskOnesZeros? cVal | return .rfl
  let nE := mkNatLit n
  let q := mkNatLit (1 <<< n)
  if k == 0 then
    let e' ← Sym.share <| mkNatMod x q
    let thm := if flipped then ``Lean.Grind.Nat.ones_and_eq_mod else ``Lean.Grind.Nat.and_eq_mod
    let h := mkApp6 (mkConst thm) x c q nE (mkNatEqRefl c) (mkNatEqRefl q)
    return .step e' h
  else
    let kE := mkNatLit k
    let p := mkNatLit (1 <<< k)
    let e' ← Sym.share <| mkNatMul (mkNatMod (mkNatDiv x p) q) p
    let thm := if flipped then ``Lean.Grind.Nat.ones_zeros_and_eq_div_mod_mul else ``Lean.Grind.Nat.and_eq_div_mod_mul
    let h := mkApp9 (mkConst thm) x c p q kE nE (mkNatEqRefl c) (mkNatEqRefl p) (mkNatEqRefl q)
    return .step e' h

/--
Rewriter for the `[grind hom]` rules and the builtin simprocs, with the stop condition:
`grind` internalizes terms bottom-up, so when no rule applies to a term that is already
in the E-graph, the term and all its subterms have already been processed by the engine,
and there is nothing to do at any depth. Traversal cost is thus proportional to the new
terms produced by the rewriting, not to the size of the input term. The stop applies to
the root as well, since `grind` creates its E-node before calling the solver hooks; the
root is rewritten only if a rule matches it as written, and then the traversal continues
through the new terms the rule produced.

Stopping at an E-graph term loses no equality: its normal form was pushed when it was
internalized, and the E-graph communicates that equality to the solvers. What is skipped is
the application of a rule at the parent whose left-hand side matches only the child's normal
form, e.g. `Nat.mod_mul_mod` on `((x <<< m).toNat <<< n) % 2 ^ w` after `(x <<< m).toNat`
was rewritten to `x.toNat * 2 ^ m % 2 ^ w`. This matters only when the solver cannot
reproduce the rule's effect from the equality, as here with the variable factor `2 ^ n`
(`cutsat` proves the same goal for a literal `n`). Injections written on proper subterms
of the goal are the usual source; the intended use, the injection at the top of a
source-domain term, builds the whole image within one traversal. An injection that factors
through another one (`Int16.toInt` maps to `toBitVec.toInt`) has a second consequence: if
`t.toBitVec` is already in the E-graph when `t.toInt` is rewritten, the rules for the
signed image of `t.toBitVec`'s normal form never fire, and the `=`-injection only produces
the unsigned one. Such types need direct rules into the final target.

Ground terms are evaluated first: the injections produce ground subterms such as
`63 % 2 ^ 64` for the literal `63#64`, and the literal-based simprocs (e.g.
`andMaskSimproc`) must see the evaluated form within the same traversal.
-/
private def mkRewriter : GoalM Sym.Simp.Simproc := do
  let s ← get
  -- `grind` keeps bit-vector literals in `OfNat.ofNat` form.
  let rw := Sym.Simp.evalGround { bitVecOfNat := false } <|> (← getThms).rewrite <|> andMaskSimproc
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
  -- The stored type of a fact may differ from the inferred type of its proof by
  -- `zetaDelta` and ground evaluation, which `isDefEq` cannot always replay.
  let fact ← mkEqMPCore eq t hEqProp (← mkEqProof a b)
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
  let fact ← mkEqMPCore (mkNot eq) (mkNot t) (← mkCongrArg (mkConst ``Not) hEqProp) hne
  let generation := max (← getGeneration a) (← getGeneration b)
  trace_goal[grind.hom] "{mkNot eq}\n===>\n{mkNot t}"
  addNewRawFact fact (mkNot t) generation .input .other

builtin_initialize
  homExt.setMethods
    (internalize := Homo.internalize)
    (newEq       := Homo.processNewEq)
    (newDiseq    := Homo.processNewDiseq)

end Lean.Meta.Grind.Homo
