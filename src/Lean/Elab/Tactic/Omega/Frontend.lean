/-
Copyright (c) 2023 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
prelude
import Lean.Elab.Tactic.Omega.Core
import Lean.Elab.Tactic.FalseOrByContra
import Lean.Meta.Tactic.Cases
import Lean.Elab.Tactic.Config

/-!
# Frontend to the `omega` tactic.

See `Lean.Elab.Tactic.Omega` for an overview of the tactic.
-/

open Lean Meta Omega

namespace Lean.Elab.Tactic.Omega

/--
Allow elaboration of `OmegaConfig` arguments to tactics.
-/
declare_config_elab elabOmegaConfig Lean.Meta.Omega.OmegaConfig

/-- Match on the two defeq expressions for successor: `n+1`, `n.succ`. -/
def succ? (e : Expr) : Option Expr :=
  match e.getAppFnArgs with
  | (``Nat.succ, #[n]) => some n
  | (``HAdd.hAdd, #[_, _, _, _, a, b]) => do
     if b == toExpr (1 : Nat) then some a else none
  | _ => none

/--
A partially processed `omega` context.

We have:
* a `Problem` representing the integer linear constraints extracted so far, and their proofs
* the unprocessed `facts : List Expr` taken from the local context,
* the unprocessed `disjunctions : List Expr`,
  which will only be split one at a time if we can't otherwise find a contradiction.

We begin with `facts := ← getLocalHyps` and `problem := .trivial`,
and progressively process the facts.

As we process the facts, we may generate additional facts
(e.g. about coercions and integer divisions).
To avoid duplicates, we maintain a `HashSet` of previously processed facts.
-/
structure MetaProblem where
  /-- An integer linear arithmetic problem. -/
  problem : Problem := {}
  /-- Pending facts which have not been processed yet. -/
  facts : List Expr := []
  /--
  Pending disjunctions, which we will case split one at a time if we can't get a contradiction.
  -/
  disjunctions : List Expr := []
  /-- Facts which have already been processed; we keep these to avoid duplicates. -/
  processedFacts : Std.HashSet Expr := ∅

/-- Construct the `rfl` proof that `lc.eval atoms = e`. -/
def mkEvalRflProof (e : Expr) (lc : LinearCombo) : OmegaM Expr := do
  mkEqReflWithExpectedType e (mkApp2 (.const ``LinearCombo.eval []) (toExpr lc) (← atomsCoeffs))

/-- If `e : Expr` is the `n`-th atom, construct the proof that
`e = (coordinate n).eval atoms`. -/
def mkCoordinateEvalAtomsEq (e : Expr) (n : Nat) : OmegaM Expr := do
  if n < 10 then
    let atoms ← atoms
    let tail ← mkListLit (.const ``Int []) atoms[n+1:].toArray.toList
    let lem := .str ``LinearCombo s!"coordinate_eval_{n}"
    mkEqSymm (mkAppN (.const lem []) (atoms[:n+1].toArray.push tail))
  else
    let atoms ← atomsCoeffs
    let n := toExpr n
    -- Construct the `rfl` proof that `e = (atoms.get? n).getD 0`
    let eq ← mkEqReflWithExpectedType e (mkApp2 (.const ``Coeffs.get []) atoms n)
    mkEqTrans eq (← mkEqSymm (mkApp2 (.const ``LinearCombo.coordinate_eval []) n atoms))

/-- Construct the linear combination (and its associated proof and new facts) for an atom. -/
def mkAtomLinearCombo (e : Expr) : OmegaM (LinearCombo × OmegaM Expr × Std.HashSet Expr) := do
  let (n, facts) ← lookup e
  return ⟨LinearCombo.coordinate n, mkCoordinateEvalAtomsEq e n, facts.getD ∅⟩

mutual

/--
Wrapper for `asLinearComboImpl`,
using a cache for previously visited expressions.

Gives a small (10%) speedup in testing.
I tried using a pointer based cache,
but there was never enough subexpression sharing to make it effective.
-/
partial def asLinearCombo (e : Expr) : OmegaM (LinearCombo × OmegaM Expr × Std.HashSet Expr) := do
  let cache ← get
  match cache.get? e with
  | some (lc, prf) =>
    trace[omega] "Found in cache: {e}"
    return (lc, prf, ∅)
  | none =>
    let (lc, proof, r) ← asLinearComboImpl e
    modifyThe Cache fun cache => (cache.insert e (lc, proof.run' cache))
    pure (lc, proof, r)

/--
Translates an expression into a `LinearCombo`.
Also returns:
* a proof that this linear combo evaluated at the atoms is equal to the original expression
* a list of new facts which should be recorded:
  * for each new atom `a` of the form `((x : Nat) : Int)`, the fact that `0 ≤ a`
  * for each new atom `a` of the form `x / k`, for `k` a positive numeral, the facts that
    `k * a ≤ x < (k + 1) * a`
  * for each new atom of the form `((a - b : Nat) : Int)`, the fact:
    `b ≤ a ∧ ((a - b : Nat) : Int) = a - b ∨ a < b ∧ ((a - b : Nat) : Int) = 0`

We also transform the expression as we descend into it:
* pushing coercions: `↑(x + y)`, `↑(x * y)`, `↑(x / k)`, `↑(x % k)`, `↑k`
* unfolding `emod`: `x % k` → `x - x / k`
-/
partial def asLinearComboImpl (e : Expr) : OmegaM (LinearCombo × OmegaM Expr × Std.HashSet Expr) := do
  trace[omega] "processing {e}"
  match groundInt? e with
  | some i =>
    let lc := {const := i}
    return ⟨lc, mkEvalRflProof e lc, ∅⟩
  | none =>
    if e.isFVar then
      if let some v ← e.fvarId!.getValue? then
        rewrite e (← mkEqReflWithExpectedType e v)
      else
        mkAtomLinearCombo e
    else match e.getAppFnArgs with
  | (``HAdd.hAdd, #[_, _, _, _, e₁, e₂]) => do
    let (l₁, prf₁, facts₁) ← asLinearCombo e₁
    let (l₂, prf₂, facts₂) ← asLinearCombo e₂
    let prf : OmegaM Expr := do
      let add_eval :=
        mkApp3 (.const ``LinearCombo.add_eval []) (toExpr l₁) (toExpr l₂) (← atomsCoeffs)
      mkEqTrans
        (← mkAppM ``Int.add_congr #[← prf₁, ← prf₂])
        (← mkEqSymm add_eval)
    pure (l₁ + l₂, prf, facts₁.union facts₂)
  | (``HSub.hSub, #[_, _, _, _, e₁, e₂]) => do
    let (l₁, prf₁, facts₁) ← asLinearCombo e₁
    let (l₂, prf₂, facts₂) ← asLinearCombo e₂
    let prf : OmegaM Expr := do
      let sub_eval :=
        mkApp3 (.const ``LinearCombo.sub_eval []) (toExpr l₁) (toExpr l₂) (← atomsCoeffs)
      mkEqTrans
        (← mkAppM ``Int.sub_congr #[← prf₁, ← prf₂])
        (← mkEqSymm sub_eval)
    pure (l₁ - l₂, prf, facts₁.union facts₂)
  | (``Neg.neg, #[_, _, e']) => do
    let (l, prf, facts) ← asLinearCombo e'
    let prf' : OmegaM Expr := do
      let neg_eval := mkApp2 (.const ``LinearCombo.neg_eval []) (toExpr l) (← atomsCoeffs)
      mkEqTrans
        (← mkAppM ``Int.neg_congr #[← prf])
        (← mkEqSymm neg_eval)
    pure (-l, prf', facts)
  | (``HMul.hMul, #[_, _, _, _, x, y]) =>
    -- If we decide not to expand out the multiplication,
    -- we have to revert the `OmegaM` state so that any new facts about the factors
    -- can still be reported when they are visited elsewhere.
    let r? ← commitWhen do
      let (xl, xprf, xfacts) ← asLinearCombo x
      let (yl, yprf, yfacts) ← asLinearCombo y
      if xl.coeffs.isZero ∨ yl.coeffs.isZero then
        let prf : OmegaM Expr := do
          let h ← mkDecideProof (mkApp2 (.const ``Or [])
            (.app (.const ``Coeffs.isZero []) (toExpr xl.coeffs))
            (.app (.const ``Coeffs.isZero []) (toExpr yl.coeffs)))
          let mul_eval :=
            mkApp4 (.const ``LinearCombo.mul_eval []) (toExpr xl) (toExpr yl) (← atomsCoeffs) h
          mkEqTrans
            (← mkAppM ``Int.mul_congr #[← xprf, ← yprf])
            (← mkEqSymm mul_eval)
        pure (some (LinearCombo.mul xl yl, prf, xfacts.union yfacts), true)
      else
        pure (none, false)
    match r? with
    | some r => pure r
    | none => mkAtomLinearCombo e
  | (``HMod.hMod, #[_, _, _, _, n, k]) =>
    match groundNat? k with
    | some k' => do
      let k' := toExpr (k' : Int)
      rewrite (← mkAppM ``HMod.hMod #[n, k']) (mkApp2 (.const ``Int.emod_def []) n k')
    | none => mkAtomLinearCombo e
  | (``HDiv.hDiv, #[_, _, _, _, x, z]) =>
    match groundInt? z with
    | some 0 => rewrite e (mkApp (.const ``Int.ediv_zero []) x)
    | some i => do
      let e' ← mkAppM ``HDiv.hDiv #[x, toExpr i]
      if i < 0 then
        rewrite e' (mkApp2 (.const ``Int.ediv_neg []) x (toExpr (-i)))
      else
        mkAtomLinearCombo e'
    | _ => mkAtomLinearCombo e
  | (``Min.min, #[_, _, a, b]) =>
    if (← cfg).splitMinMax then
      rewrite e (mkApp2 (.const ``Int.min_def []) a b)
    else
      mkAtomLinearCombo e
  | (``Max.max, #[_, _, a, b]) =>
    if (← cfg).splitMinMax then
      rewrite e (mkApp2 (.const ``Int.max_def []) a b)
    else
      mkAtomLinearCombo e
  | (``HPow.hPow, #[_, _, _, _, b, k]) =>
    match succ? k with /- match for `e+1` and `e.succ` -/
    | none => mkAtomLinearCombo e
    | some k' =>
        match groundInt? b with
        | some _ => rewrite e (mkApp2 (.const ``Int.pow_succ []) b k')
        | none => mkAtomLinearCombo e
  | (``Nat.cast, #[α, i, n]) =>
      match_expr α with
      | Int => handleNatCast e i n
      | _ => mkAtomLinearCombo e
  | (``Prod.fst, #[α, β, p]) => match p with
    | .app (.app (.app (.app (.const ``Prod.mk [u, v]) _) _) x) y =>
      rewrite e (mkApp4 (.const ``Prod.fst_mk [u, v]) α x β y)
    | _ => mkAtomLinearCombo e
  | (``Prod.snd, #[α, β, p]) => match p with
    | .app (.app (.app (.app (.const ``Prod.mk [u, v]) _) _) x) y =>
      rewrite e (mkApp4 (.const ``Prod.snd_mk [u, v]) α x β y)
    | _ => mkAtomLinearCombo e
  | _ => mkAtomLinearCombo e
where
  /--
  Apply a rewrite rule to an expression, and interpret the result as a `LinearCombo`.
  (We're not rewriting any subexpressions here, just the top level, for efficiency.)
  -/
  rewrite (lhs rw : Expr) : OmegaM (LinearCombo × OmegaM Expr × Std.HashSet Expr) := do
    trace[omega] "rewriting {lhs} via {rw} : {← inferType rw}"
    match (← inferType rw).eq? with
    | some (_, _lhs', rhs) =>
      let (lc, prf, facts) ← asLinearCombo rhs
      let prf' : OmegaM Expr := do mkEqTrans rw (← prf)
      pure (lc, prf', facts)
    | none => panic! "Invalid rewrite rule in 'asLinearCombo'"
  handleNatCast (e i n : Expr) : OmegaM (LinearCombo × OmegaM Expr × Std.HashSet Expr) := do
    match n with
    | .fvar h =>
      if let some v ← h.getValue? then
        rewrite e (← mkEqReflWithExpectedType e
          (mkApp3 (.const ``Nat.cast [0]) (.const ``Int []) i v))
      else
        mkAtomLinearCombo e
    | _ => match n.getAppFnArgs with
    | (``Nat.succ, #[n]) => rewrite e (.app (.const ``Int.ofNat_succ []) n)
    | (``HAdd.hAdd, #[_, _, _, _, a, b]) => rewrite e (mkApp2 (.const ``Int.ofNat_add []) a b)
    | (``HMul.hMul, #[_, _, _, _, a, b]) =>
      let (lc, prf, r) ← rewrite e (mkApp2 (.const ``Int.ofNat_mul []) a b)
      -- Add the fact that the multiplication is non-negative.
      pure (lc, prf, r.insert (mkApp2 (.const ``Int.ofNat_mul_nonneg []) a b))
    | (``HDiv.hDiv, #[_, _, _, _, a, b]) => rewrite e (mkApp2 (.const ``Int.ofNat_ediv []) a b)
    | (``OfNat.ofNat, #[_, n, _]) => rewrite e (.app (.const ``Int.natCast_ofNat []) n)
    | (``HMod.hMod, #[_, _, _, _, a, b]) => rewrite e (mkApp2 (.const ``Int.ofNat_emod []) a b)
    | (``HSub.hSub, #[_, _, _, _, mkApp6 (.const ``HSub.hSub _) _ _ _ _ a b, c]) =>
      rewrite e (mkApp3 (.const ``Int.ofNat_sub_sub []) a b c)
    | (``HPow.hPow, #[_, _, _, _, a, b]) =>
      match groundNat? a with
      | some _ => rewrite e (mkApp2 (.const ``Int.ofNat_pow []) a b)
      | none => mkAtomLinearCombo e
    | (``Prod.fst, #[_, β, p]) => match p with
      | .app (.app (.app (.app (.const ``Prod.mk [0, v]) _) _) x) y =>
        rewrite e (mkApp3 (.const ``Int.ofNat_fst_mk [v]) β x y)
      | _ => mkAtomLinearCombo e
    | (``Prod.snd, #[α, _, p]) => match p with
      | .app (.app (.app (.app (.const ``Prod.mk [u, 0]) _) _) x) y =>
        rewrite e (mkApp3 (.const ``Int.ofNat_snd_mk [u]) α x y)
      | _ => mkAtomLinearCombo e
    | (``Min.min, #[_, _, a, b]) => rewrite e (mkApp2 (.const ``Int.ofNat_min []) a b)
    | (``Max.max, #[_, _, a, b]) => rewrite e (mkApp2 (.const ``Int.ofNat_max []) a b)
    | (``Int.toNat, #[n]) => rewrite e (mkApp (.const ``Int.toNat_eq_max []) n)
    | (``HShiftLeft.hShiftLeft, #[_, _, _, _, a, b]) =>
      rewrite e (mkApp2 (.const ``Int.ofNat_shiftLeft_eq []) a b)
    | (``HShiftRight.hShiftRight, #[_, _, _, _, a, b]) =>
      rewrite e (mkApp2 (.const ``Int.ofNat_shiftRight_eq_div_pow []) a b)
    | (``Int.natAbs, #[n]) =>
      if (← cfg).splitNatAbs then
        rewrite e (mkApp (.const ``Int.ofNat_natAbs []) n)
      else
        mkAtomLinearCombo e
    | (``Fin.val, #[n, x]) =>
      handleFinVal e i n x
    | _ => mkAtomLinearCombo e
  handleFinVal (e i n x : Expr) : OmegaM (LinearCombo × OmegaM Expr × Std.HashSet Expr) := do
    match x with
    | .fvar h =>
      if let some v ← h.getValue? then
        rewrite e (← mkEqReflWithExpectedType e
          (mkApp3 (.const ``Nat.cast [0]) (.const ``Int []) i (mkApp2 (.const ``Fin.val []) n v)))
      else
        mkAtomLinearCombo e
    | _ => match x.getAppFnArgs, n.nat? with
      | (``HAdd.hAdd, #[_, _, _, _, a, b]), _ =>
        rewrite e (mkApp3 (.const ``Fin.ofNat_val_add []) n a b)
      | (``HMul.hMul, #[_, _, _, _, a, b]), _ =>
        rewrite e (mkApp3 (.const ``Fin.ofNat_val_mul []) n a b)
      | (``HSub.hSub, #[_, _, _, _, a, b]), some _ =>
        -- Only do this rewrite if `n` is a numeral.
        rewrite e (mkApp3 (.const ``Fin.ofNat_val_sub []) n a b)
      | (``OfNat.ofNat, #[_, y, _]), some m =>
        -- Only do this rewrite if `n` is a nonzero numeral.
        if m = 0 then
          mkAtomLinearCombo e
        else
          match y with
          | .lit (.natVal y) =>
            rewrite e (mkApp4 (.const ``Fin.ofNat_val_natCast [])
              (toExpr (m - 1)) (toExpr y) (.lit (.natVal (y % m))) (← mkEqRefl (toExpr (y % m))))
          | _ =>
            -- This shouldn't happen, we obtained `y` from `OfNat.ofNat`
            mkAtomLinearCombo e
      | _, _ => mkAtomLinearCombo e

end
namespace MetaProblem

/-- The trivial `MetaProblem`, with no facts to process and a trivial `Problem`. -/
def trivial : MetaProblem where
  problem := {}

instance : Inhabited MetaProblem := ⟨trivial⟩

/--
Add an integer equality to the `Problem`.

We solve equalities as they are discovered, as this often results in an earlier contradiction.
-/
def addIntEquality (p : MetaProblem) (h x : Expr) : OmegaM MetaProblem := do
  let (lc, prf, facts) ← asLinearCombo x
  let newFacts : Std.HashSet Expr := facts.fold (init := ∅) fun s e =>
    if p.processedFacts.contains e then s else s.insert e
  trace[omega] "Adding proof of {lc} = 0"
  pure <|
  { p with
    facts := newFacts.toList ++ p.facts
    problem := ← (p.problem.addEquality lc.const lc.coeffs
      (some do mkEqTrans (← mkEqSymm (← prf)) h)) |>.solveEqualities }

/--
Add an integer inequality to the `Problem`.

We solve equalities as they are discovered, as this often results in an earlier contradiction.
-/
def addIntInequality (p : MetaProblem) (h y : Expr) : OmegaM MetaProblem := do
  let (lc, prf, facts) ← asLinearCombo y
  let newFacts : Std.HashSet Expr := facts.fold (init := ∅) fun s e =>
    if p.processedFacts.contains e then s else s.insert e
  trace[omega] "Adding proof of {lc} ≥ 0"
  pure <|
  { p with
    facts := newFacts.toList ++ p.facts
    problem := ← (p.problem.addInequality lc.const lc.coeffs
      (some do mkAppM ``le_of_le_of_eq #[h, (← prf)])) |>.solveEqualities }

/-- Given a fact `h` with type `¬ P`, return a more useful fact obtained by pushing the negation. -/
def pushNot (h P : Expr) : MetaM (Option Expr) := do
  let P ← whnfR P
  trace[omega] "pushing negation: {P}"
  match P with
  | .forallE _ t b _ =>
    if (← isProp t) && (← isProp b) then
     return some (mkApp4 (.const ``Decidable.and_not_of_not_imp []) t b
      (.app (.const ``Classical.propDecidable []) t) h)
    else
      return none
  | .app _ _ =>
    match_expr P with
    | LT.lt α _ x y => match_expr α with
      | Nat => return some (mkApp3 (.const ``Nat.le_of_not_lt []) x y h)
      | Int => return some (mkApp3 (.const ``Int.le_of_not_lt []) x y h)
      | Fin n => return some (mkApp4 (.const ``Fin.le_of_not_lt []) n x y h)
      | _ => return none
    | LE.le α _ x y => match_expr α with
      | Nat => return some (mkApp3 (.const ``Nat.lt_of_not_le []) x y h)
      | Int => return some (mkApp3 (.const ``Int.lt_of_not_le []) x y h)
      | Fin n => return some (mkApp4 (.const ``Fin.lt_of_not_le []) n x y h)
      | _ => return none
    | Eq α x y => match_expr α with
      | Nat => return some (mkApp3 (.const ``Nat.lt_or_gt_of_ne []) x y h)
      | Int => return some (mkApp3 (.const ``Int.lt_or_gt_of_ne []) x y h)
      | Fin n => return some (mkApp4 (.const ``Fin.lt_or_gt_of_ne []) n x y h)
      | _ => return none
    | Dvd.dvd α _ k x => match_expr α with
      | Nat => return some (mkApp3 (.const ``Nat.emod_pos_of_not_dvd []) k x h)
      | Int =>
        -- This introduces a disjunction that could be avoided by checking `k ≠ 0`.
        return some (mkApp3 (.const ``Int.emod_pos_of_not_dvd []) k x h)
      | _ => return none
    | Prod.Lex _ _ _ _ _ _ => return some (← mkAppM ``Prod.of_not_lex #[h])
    | Not P =>
      return some (mkApp3 (.const ``Decidable.of_not_not []) P
        (.app (.const ``Classical.propDecidable []) P) h)
    | And P Q =>
      return some (mkApp5 (.const ``Decidable.or_not_not_of_not_and []) P Q
        (.app (.const ``Classical.propDecidable []) P)
        (.app (.const ``Classical.propDecidable []) Q) h)
    | Or P Q =>
      return some (mkApp3 (.const ``and_not_not_of_not_or []) P Q h)
    | Iff P Q =>
      return some (mkApp5 (.const ``Decidable.and_not_or_not_and_of_not_iff []) P Q
        (.app (.const ``Classical.propDecidable []) P)
        (.app (.const ``Classical.propDecidable []) Q) h)
    | _ => return none
  | _ => return none

/--
Parse an `Expr` and extract facts, also returning the number of new facts found.
-/
partial def addFact (p : MetaProblem) (h : Expr) : OmegaM (MetaProblem × Nat) := do
  if ! p.problem.possible then
    return (p, 0)
  else
    let t ← instantiateMVars (← whnfR (← inferType h))
    trace[omega] "adding fact: {t}"
    match t with
    | .forallE _ x y _ =>
      if ← pure t.isArrow <&&> isProp x <&&> isProp y then
        p.addFact (mkApp4 (.const ``Decidable.not_or_of_imp []) x y
          (.app (.const ``Classical.propDecidable []) x) h)
      else
        trace[omega] "rejecting forall: it's not an arrow, or not propositional"
        return (p, 0)
    | .app _ _ =>
      match_expr t with
      | Eq α x y =>
        match_expr α with
        | Int =>
          match y.int? with
          | some 0 => pure (← p.addIntEquality h x, 1)
          | _ => p.addFact (mkApp3 (.const ``Int.sub_eq_zero_of_eq []) x y h)
        | Nat => p.addFact (mkApp3 (.const ``Int.ofNat_congr []) x y h)
        | Fin n => p.addFact (mkApp4 (.const ``Fin.val_congr []) n x y h)
        | _ => pure (p, 0)
      | LE.le α _ x y =>
        match_expr α with
        | Int =>
          match x.int? with
          | some 0 => pure (← p.addIntInequality h y, 1)
          | _ => p.addFact (mkApp3 (.const ``Int.sub_nonneg_of_le []) y x h)
        | Nat => p.addFact (mkApp3 (.const ``Int.ofNat_le_of_le []) x y h)
        | Fin n => p.addFact (mkApp4 (.const ``Fin.val_le_of_le []) n x y h)
        | _ => pure (p, 0)
      | LT.lt α _ x y =>
        match_expr α with
        | Int => p.addFact (mkApp3 (.const ``Int.add_one_le_of_lt []) x y h)
        | Nat => p.addFact (mkApp3 (.const ``Int.ofNat_lt_of_lt []) x y h)
        | Fin n => p.addFact (mkApp4 (.const ``Fin.val_add_one_le_of_lt []) n x y h)
        | _ => pure (p, 0)
      | GT.gt α _ x y =>
        match_expr α with
        | Int => p.addFact (mkApp3 (.const ``Int.lt_of_gt []) x y h)
        | Nat => p.addFact (mkApp3 (.const ``Nat.lt_of_gt []) x y h)
        | Fin n => p.addFact (mkApp4 (.const ``Fin.val_add_one_le_of_gt []) n x y h)
        | _ => pure (p, 0)
      | GE.ge α _ x y =>
        match_expr α with
        | Int => p.addFact (mkApp3 (.const ``Int.le_of_ge []) x y h)
        | Nat => p.addFact (mkApp3 (.const ``Nat.le_of_ge []) x y h)
        | Fin n => p.addFact (mkApp4 (.const ``Fin.val_le_of_ge []) n x y h)
        | _ => pure (p, 0)
      | Ne α x y =>
        match_expr α with
        | Int => p.addFact (mkApp3 (.const ``Int.lt_or_gt_of_ne []) x y h)
        | Nat => p.addFact (mkApp3 (.const ``Nat.lt_or_gt_of_ne []) x y h)
        | _ => pure (p, 0)
      | Dvd.dvd α _ k x =>
        match_expr α with
        | Int => p.addFact (mkApp3 (.const ``Int.emod_eq_zero_of_dvd []) k x h)
        | Nat => p.addFact (mkApp3 (.const ``Nat.mod_eq_zero_of_dvd []) k x h)
        | _ => pure (p, 0)
      | Not P => match ← pushNot h P with
        | none => return (p, 0)
        | some h' => p.addFact h'
      | Prod.Lex _ _ _ _ _ _ => p.addFact (← mkAppM ``Prod.of_lex #[h])
      | And t₁ t₂ => do
          let (p₁, n₁) ← p.addFact (mkApp3 (.const ``And.left []) t₁ t₂ h)
          let (p₂, n₂) ← p₁.addFact (mkApp3 (.const ``And.right []) t₁ t₂ h)
          return (p₂, n₁ + n₂)
      | Exists α P =>
        p.addFact (mkApp3 (.const ``Exists.choose_spec [← getLevel α]) α P h)
      | Subtype α P =>
        p.addFact (mkApp3 (.const ``Subtype.property [← getLevel α]) α P h)
      | Iff P₁ P₂ =>
        p.addFact (mkApp4 (.const ``Decidable.and_or_not_and_not_of_iff [])
          P₁ P₂ (.app (.const ``Classical.propDecidable []) P₂) h)
      | Or _ _ =>
        if (← cfg).splitDisjunctions then
          return ({ p with disjunctions := p.disjunctions.insert h }, 1)
        else
          return (p, 0)
      | _ => pure (p, 0)
    | _ => pure (p, 0)

/--
Process all the facts in a `MetaProblem`, returning the new problem, and the number of new facts.

This is partial because new facts may be generated along the way.
-/
partial def processFacts (p : MetaProblem) : OmegaM (MetaProblem × Nat) := do
  match p.facts with
  | [] => pure (p, 0)
  | h :: t =>
    if p.processedFacts.contains h then
      processFacts { p with facts := t }
    else
      let (p₁, n₁) ← MetaProblem.addFact { p with
        facts := t
        processedFacts := p.processedFacts.insert h } h
      let (p₂, n₂) ← p₁.processFacts
      return (p₂, n₁ + n₂)

end MetaProblem

/--
Given `p : P ∨ Q` (or any inductive type with two one-argument constructors),
split the goal into two subgoals:
one containing the hypothesis `h : P` and another containing `h : Q`.
-/
def cases₂ (mvarId : MVarId) (p : Expr) (hName : Name := `h) :
    MetaM ((MVarId × FVarId) × (MVarId × FVarId)) := do
  let mvarId ← mvarId.assert `hByCases (← inferType p) p
  let (fvarId, mvarId) ← mvarId.intro1
  let #[s₁, s₂] ← mvarId.cases fvarId #[{ varNames := [hName] }, { varNames := [hName] }] |
    throwError "'cases' tactic failed, unexpected number of subgoals"
  let #[Expr.fvar f₁ ..] ← pure s₁.fields
    | throwError "'cases' tactic failed, unexpected new hypothesis"
  let #[Expr.fvar f₂ ..] ← pure s₂.fields
    | throwError "'cases' tactic failed, unexpected new hypothesis"
  return ((s₁.mvarId, f₁), (s₂.mvarId, f₂))

/--
Helpful error message when omega cannot find a solution
-/
def formatErrorMessage (p : Problem) : OmegaM MessageData := do
  if p.possible then
    if p.isEmpty then
      return m!"No usable constraints found. You may need to unfold definitions so `omega` can see \
      linear arithmetic facts about `Nat` and `Int`, which may also involve multiplication, \
      division, and modular remainder by constants."
    else
      let as ← atoms
      return .ofLazyM (es := as) do
        let mask ← mentioned as p.constraints
        let names ← varNames mask
        return m!"a possible counterexample may satisfy the constraints\n" ++
          m!"{prettyConstraints names p.constraints}\nwhere\n{prettyAtoms names as mask}"
  else
    -- formatErrorMessage should not be used in this case
    return "it is trivially solvable"
where
  varNameOf (i : Nat) : String :=
    let c : Char := .ofNat ('a'.toNat + (i % 26))
    let suffix := if i < 26 then "" else s!"_{i / 26}"
    s!"{c}{suffix}"

  inScope (s : String) : MetaM Bool := do
    let n := .mkSimple s
    if (← resolveGlobalName n).isEmpty then
      if ((← getLCtx).findFromUserName? n).isNone then
        return false
    return true

  -- Assign ascending names a, b, c, …, z, a1 … to all atoms mentioned according to the mask
  -- but avoid names in the local or global scope
  varNames (mask : Array Bool) : MetaM (Array String) := do
    let mut names := #[]
    let mut next := 0
    for h : i in [:mask.size] do
      if mask[i] then
        while ← inScope (varNameOf next) do next := next + 1
        names := names.push (varNameOf next)
        next := next + 1
      else
        names := names.push "(masked)"
    return names

  -- We sort the constraints; otherwise the order is dependent on details of the hashing
  -- and this can cause test suite output churn
  prettyConstraints (names : Array String) (constraints : Std.HashMap Coeffs Fact) : String :=
    constraints.toList
      |>.toArray
      |>.qsort (·.1 < ·.1)
      |>.map (fun ⟨coeffs, ⟨_, cst, _⟩⟩ => "  " ++ prettyConstraint (prettyCoeffs names coeffs) cst)
      |>.toList
      |> "\n".intercalate

  prettyConstraint (e : String) : Constraint → String
    | ⟨none, none⟩ => s!"{e} is unconstrained" -- should not happen in error messages
    | ⟨none, some y⟩ => s!"{e} ≤ {y}"
    | ⟨some x, none⟩ => s!"{e} ≥ {x}"
    | ⟨some x, some y⟩ =>
      if y < x then "∅" else -- should not happen in error messages
      s!"{x} ≤ {e} ≤ {y}"

  prettyCoeffs (names : Array String) (coeffs : Coeffs) : String :=
    coeffs.toList.enum
      |>.filter (fun (_,c) => c ≠ 0)
      |>.enum
      |>.map (fun (j, (i,c)) =>
        (if j > 0 then if c > 0 then " + " else " - " else if c > 0 then "" else "- ") ++
        (if Int.natAbs c = 1 then names[i]! else s!"{c.natAbs}*{names[i]!}"))
      |> String.join

  mentioned (atoms : Array Expr) (constraints : Std.HashMap Coeffs Fact) : MetaM (Array Bool) := do
    let initMask := Array.mkArray atoms.size false
    return constraints.fold (init := initMask) fun mask coeffs _ =>
      coeffs.enum.foldl (init := mask) fun mask (i, c) =>
        if c = 0 then mask else mask.set! i true

  prettyAtoms (names : Array String) (atoms : Array Expr) (mask : Array Bool) : MessageData :=
    (Array.zip names atoms).toList.enum
      |>.filter (fun (i, _) => mask.getD i false)
      |>.map (fun (_, (n, a)) => m!" {n} := {a}")
      |> m!"\n".joinSep

mutual

/--
Split a disjunction in a `MetaProblem`, and if we find a new usable fact
call `omegaImpl` in both branches.
-/
partial def splitDisjunction (m : MetaProblem) (g : MVarId) : OmegaM Unit := g.withContext do
  match m.disjunctions with
    | [] => throwError "omega could not prove the goal:\n{← formatErrorMessage m.problem}"
    | h :: t =>
      trace[omega] "Case splitting on {← inferType h}"
      let ctx ← getMCtx
      let (⟨g₁, h₁⟩, ⟨g₂, h₂⟩) ← cases₂ g h
      trace[omega] "Adding facts:\n{← g₁.withContext <| inferType (.fvar h₁)}"
      let m₁ := { m with facts := [.fvar h₁], disjunctions := t }
      let r ← withoutModifyingState do
        let (m₁, n) ← g₁.withContext m₁.processFacts
        if 0 < n then
          omegaImpl m₁ g₁
          pure true
        else
          pure false
      if r then
        trace[omega] "Adding facts:\n{← g₂.withContext <| inferType (.fvar h₂)}"
        let m₂ := { m with facts := [.fvar h₂], disjunctions := t }
        omegaImpl m₂ g₂
      else
        trace[omega] "No new facts found."
        setMCtx ctx
        splitDisjunction { m with disjunctions := t } g

/-- Implementation of the `omega` algorithm, and handling disjunctions. -/
partial def omegaImpl (m : MetaProblem) (g : MVarId) : OmegaM Unit := g.withContext do
  let (m, _) ← m.processFacts
  guard m.facts.isEmpty
  let p := m.problem
  trace[omega] "Extracted linear arithmetic problem:\nAtoms: {← atomsList}\n{p}"
  let p' ← if p.possible then p.elimination else pure p
  trace[omega] "After elimination:\nAtoms: {← atomsList}\n{p'}"
  match p'.possible, p'.proveFalse?, p'.proveFalse?_spec with
  | true, _, _ =>
    splitDisjunction m g
  | false, .some prf, _ =>
    trace[omega] "Justification:\n{p'.explanation?.get}"
    let prf ← instantiateMVars (← prf)
    trace[omega] "omega found a contradiction, proving {← inferType prf}"
    g.assign prf

end

/--
Given a collection of facts, try prove `False` using the omega algorithm,
and close the goal using that.
-/
def omega (facts : List Expr) (g : MVarId) (cfg : OmegaConfig := {}) : MetaM Unit :=
  OmegaM.run (omegaImpl { facts } g) cfg

open Lean Elab Tactic Parser.Tactic

/-- The `omega` tactic, for resolving integer and natural linear arithmetic problems. -/
def omegaTactic (cfg : OmegaConfig) : TacticM Unit := do
  liftMetaFinishingTactic fun g => do
    let some g ← g.falseOrByContra | return ()
    g.withContext do
      let hyps := (← getLocalHyps).toList
      trace[omega] "analyzing {hyps.length} hypotheses:\n{← hyps.mapM inferType}"
      omega hyps g cfg

/-- The `omega` tactic, for resolving integer and natural linear arithmetic problems. This
`TacticM Unit` frontend with default configuration can be used as an Aesop rule, for example via
the tactic call `aesop (add 50% tactic Lean.Omega.omegaDefault)`. -/
def omegaDefault : TacticM Unit := omegaTactic {}

@[builtin_tactic Lean.Parser.Tactic.omega]
def evalOmega : Tactic := fun
  | `(tactic| omega $[$cfg]?) => do
    let cfg ← elabOmegaConfig (mkOptionalNode cfg)
    omegaTactic cfg
  | _ => throwUnsupportedSyntax

builtin_initialize bvOmegaSimpExtension : SimpExtension ←
  registerSimpAttr `bv_toNat
    "simp lemmas converting `BitVec` goals to `Nat` goals, for the `bv_omega` preprocessor"
