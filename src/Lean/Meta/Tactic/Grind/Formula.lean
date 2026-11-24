/-
Copyright (c) 2026 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
public import Lean.Meta.Basic
public import Lean.Util.MonadCache
import Init.Grind.Lemmas
import Lean.Data.LBool

/-!
# Common consequences of `And` and `Or` formulas

A solver supplies a summary for each atom and a rule for combining summaries at each connective.
The folds follow the binary structure of the formula, treating every proposition other than
`And` and `Or` as an atom. Structurally equal subformulas share a summary.

For example, from `(p ∧ x ≤ 2) ∨ (x ≤ 5 ∧ q)` an arithmetic solver can infer `x ≤ 5`.
Each conjunction supplies an upper bound, and the disjunction keeps the weaker bound.
If the solver needs a proof, it can use `Summary.find?` to tell `prove` which subformulas
imply `x ≤ 5`. The solver weakens `x ≤ 2` in the left alternative, and `prove` combines
the two branches.
-/

public section
namespace Lean.Meta.Grind.Formula

variable {m : Type → Type} {ω : Type} [Monad m] [STWorld ω m] [MonadLiftT (ST ω) m]

/--
Cached inspection results for a subformula, which may occur as both a conjunct and a disjunct.
For example, take integer variables `x`, `y`, and `z`. The arithmetic hull inspects
`d` in `(d ∧ z ≤ 0) ∨ d` as follows.

* If `d` is `x ≤ 1 ∨ x ≤ 3`, both atoms are supported and both imply `x ≤ 3`.
  The entry for `d` has `supported := true` and `conjunct := .true`.
* If `d` is `x ≤ 1 ∨ y ≤ 3` for distinct variables, both atoms are still supported, but
  they bound different variables. The entry has `supported := true` and `conjunct := .false`.
  The fold skips `d` in the conjunction and can still visit it as the right disjunct.

If the source is just `z ≤ 0 ∨ d`, then `d` occurs only as a disjunct and its
`conjunct` remains `.undef` in either example.
-/
private structure Admission where
  /-- Whether the subformula can contribute before checking its use as a conjunct. -/
  supported : Bool
  /-- The decision for uses as a conjunct. `.undef` means the callback has not run for this node. -/
  conjunct : LBool := .undef
  deriving Inhabited

/-- Determine viability bottom-up before evaluating atoms. Memoize the extra check on a
conjunction's child separately so rejecting that use preserves its viability as a disjunct. -/
private partial def inspect (canContribute : Expr → Bool)
    (admitConjunct : Expr → (Expr → Bool) → m Bool) (e : Expr) : StateRefT (ExprStructMap Admission) m Admission := do
  let key : ExprStructEq := ⟨e⟩
  if let some result := (← get)[key]? then return result
  let recur := inspect canContribute admitConjunct
  let conjunct := fun c => do
    let info ← recur c
    unless info.supported do return false
    match info.conjunct with
    | .true => return true
    | .false => return false
    | .undef =>
      let nodes ← get
      let result ← liftM (admitConjunct c fun sub => nodes[(sub : ExprStructEq)]?.any (·.supported))
      modify (·.insert c { info with conjunct := Bool.toLBool result })
      return result
  let supported ← match_expr (meta := false) e with
    | And a b => pure ((← conjunct a) || (← conjunct b))
    | Or a b =>
      -- One unsupported alternative rules out the disjunction. Try the shallower one first.
      let (a, b) := if a.approxDepth ≤ b.approxDepth then (a, b) else (b, a)
      if (← recur a).supported then pure (← recur b).supported else pure false
    | _ => pure (canContribute e)
  let info := { supported : Admission }
  modify (·.insert key info)
  return info

/-- Evaluate the fold using three shortcuts. `skip?` supplies a cacheable result for a node.
`skipConjunct?` supplies a result only to the enclosing conjunction, leaving other uses of the
child free to visit it. `finishOr?` can finish a disjunction after its left child. -/
private partial def visit {σ : Type} [Nonempty σ]
    (atom : Expr → m σ) (and or : σ → σ → σ)
    (skip? skipConjunct? : Expr → Option σ) (finishOr? : σ → Option σ) (e : Expr) :
    MonadCacheT ExprStructEq σ m σ :=
  checkCache (e : ExprStructEq) fun _ => do
    if let some result := skip? e then return result
    let recur := visit atom and or skip? skipConjunct? finishOr?
    match_expr (meta := false) e with
    | And a b =>
      let child := fun e => if let some result := skipConjunct? e then pure result else recur e
      return and (← child a) (← child b)
    | Or a b =>
      let left ← recur a
      if let some result := finishOr? left then return result
      return or left (← recur b)
    | _ => liftM (atom e)

/-- The root result and the computed subformula summaries for a single fold. -/
structure Summary (σ : Type) where
  root : σ
  /-- Results keyed by structural expression equality, retained for proof reconstruction. -/
  private entries : ExprStructMap σ

/-- Find a computed subformula summary. Subformulas skipped by the fold may be absent. -/
def Summary.find? (s : Summary σ) (e : Expr) : Option σ :=
  s.entries[(e : ExprStructEq)]?

/-- Run one fold with a fresh cache and retain the cache for `Summary.find?`. -/
private def runFold (x : MonadCacheT ExprStructEq σ m σ) : m (Summary σ) := do
  let (root, entries) ← StateRefT'.run x {}
  return ⟨root, entries⟩

/--
Fold in source order using the caller's cache. On a cache miss, `known? e = some s` supplies
the summary for `e` and skips its traversal. Reuse the cache across roots when the callbacks
give each shared subformula the same meaning.
-/
def foldCachedM {σ : Type} [Nonempty σ] (atom : Expr → m σ) (and or : σ → σ → σ) (e : Expr)
    (known? : Expr → Option σ := fun _ => none) : MonadCacheT ExprStructEq σ m σ :=
  visit atom and or known? (fun _ => none) (fun _ => none) e

/-- Fold left to right with a fresh cache. The grouping of `and` and `or` follows the source
exactly, and `atom` runs once per structurally distinct atom. -/
def foldM {σ : Type} [Nonempty σ] (atom : Expr → m σ) (and or : σ → σ → σ) (e : Expr) :
    m (Summary σ) :=
  runFold (foldCachedM atom and or e)

/--
Inspect the formula before running `atom`, so an irrelevant branch can be skipped even when
evaluating its atoms would have solver effects. A conjunction needs one viable child and a
disjunction needs two. The fold then evaluates surviving atoms in source order, skipping the
right disjunct when the left summary satisfies `isEmpty`.

Atoms rejected by `canContribute` must have summary `empty`, and `isEmpty` must recognize
summaries interchangeable with `empty`. The combining rules must satisfy
`and empty empty = empty`, `or empty s = empty`, and `or s empty = empty`.

During inspection, `admitConjunct child supported` can treat a viable child as empty wherever
it occurs as a conjunct. The same child may still contribute as a disjunct. The lookup
`supported` returns true for subformulas found viable so far. A false result can also mean
that inspection skipped the subformula.
-/
def foldRelevantM {σ : Type} (canContribute : Expr → Bool) (empty : σ) (isEmpty : σ → Bool)
    (atom : Expr → m σ) (and or : σ → σ → σ) (e : Expr)
    (admitConjunct : Expr → (Expr → Bool) → m Bool := fun _ _ => pure true) : m (Summary σ) := do
  have : Nonempty σ := ⟨empty⟩
  let (root, nodes) ← StateRefT'.run (ω := ω) (inspect canContribute admitConjunct e) {}
  unless root.supported do return ⟨empty, ({} : ExprStructMap σ).insert e empty⟩
  let skip? := fun (c : Expr) => if nodes[(c : ExprStructEq)]!.supported then none else some empty
  let skipConjunct? := fun (c : Expr) => if nodes[(c : ExprStructEq)]!.conjunct == .false then some empty else none
  let finishOr? := fun x => if isEmpty x then some empty else none
  runFold (visit atom and or skip? skipConjunct? finishOr? e)

/--
Prove `motive` from `h : source`. The caller supplies `support` for this particular motive.
Each reached conjunction must have a supported child (the left is preferred), and both
alternatives of a reached disjunction must imply the motive. At each reached atom `e`,
`support e` must return `some a` and `proveAtom a e hₑ` must prove `motive` from `hₑ : e`.

The cache stores implications `e → motive` so that occurrences of `e` under different branch
hypotheses share a proof. The source and motive may use local variables and must have no
loose bound variables.
-/
partial def prove {α : Type} [MonadError m] [MonadControlT MetaM m] [MonadLiftT MetaM m]
    (source motive h : Expr) (support : Expr → Option α)
    (proveAtom : α → Expr → Expr → m Expr) : m Expr := do
  return mkApp (← (go source).run) h
where
  /-- Abstract over the hypothesis of `e` so the cached implication works in every branch. -/
  go (e : Expr) : MonadCacheT ExprStructEq Expr m Expr :=
    checkCache (e : ExprStructEq) fun _ => do
      match_expr (meta := false) e with
      | And a b =>
        if (support a).isSome then
          return mkApp4 (mkConst ``Lean.Grind.and_imp_of_left) a b motive (← go a)
        else
          return mkApp4 (mkConst ``Lean.Grind.and_imp_of_right) a b motive (← go b)
      | Or a b =>
        return mkApp5 (mkConst ``Lean.Grind.or_imp_of_imp) a b motive (← go a) (← go b)
      | _ =>
        let some value := support e
          | return ← liftM (m := m) <| throwError "unsupported atom in formula proof{indentExpr e}"
        liftM (m := m) <| withLocalDeclD `h e fun h => do mkLambdaFVars #[h] (← proveAtom value e h)

end Lean.Meta.Grind.Formula
