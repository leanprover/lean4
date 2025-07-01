/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Data.Int.Linear
import Std.Internal.Rat
import Lean.Data.PersistentArray
import Lean.Meta.Tactic.Grind.ExprPtr
import Lean.Meta.Tactic.Grind.Arith.Util
import Lean.Meta.Tactic.Grind.Arith.Cutsat.ToIntInfo
import Lean.Meta.Tactic.Grind.Arith.CommRing.Types

namespace Lean.Meta.Grind.Arith.Cutsat

export Int.Linear (Var Poly)
export Std.Internal (Rat)

deriving instance Hashable for Poly

/-!
This module implements a model-based decision procedure for linear integer arithmetic,
inspired by Section 4 of "Cutting to the Chase: Solving Linear Integer Arithmetic".
Our implementation includes several enhancements and modifications:
Key Features:
- Extended constraint support (equality and disequality)
- Optimized encoding of `Cooper-Left` rule using "big"-disjunction instead of fresh variables
- Decision variable tracking for case splits (disequalities, `Cooper-Left`, `Cooper-Right`)

Constraint Types:
We handle four categories of linear polynomial constraints (where p is a linear polynomial):
1. Equality:     `p = 0`
2. Divisibility: `d ∣ p`
3. Inequality:   `p ≤ 0`
4. Disequality:  `p ≠ 0`

Implementation Details:
- Polynomials use `Int.Linear.Poly` with sorted linear monomials (leading monomial contains max variable)
- Equalities are eliminated eagerly
- Divisibility constraints are maintained in solved form (one constraint per variable) using `Div-Solve`

Model Construction:
The procedure builds a model incrementally, resolving conflicts through constraint generation.
For example:
Given a partial model `{x := 1}` and constraint `3 ∣ 3*y + x + 1`:
- Cannot extend to `y` because `3 ∣ 3*y + 2` is unsatisfiable
- Generate implied constraint `3 ∣ x + 1`
- Force model update for `x`

Variable Assignment:
When assigning a variable `y`, we consider:
- Best upper and lower bounds (inequalities)
- Divisibility constraint
- Disequality constraints
`Cooper-Left` and `Cooper-Right` rules handle the combination of inequalities and divisibility.
For unsatisfiable disequalities p ≠ 0, we generate case split: `p + 1 ≤ 0 ∨ -p + 1 ≤ 0`

Contradiction Handling:
- Check dependency on decision variables
- If independent, use contradiction to close current grind goal
- Otherwise, trigger backtracking

Optimization:
We employ rational approximation for model construction:
- Continue with rational solutions when integer solutions aren't immediately found
- Helps identify simpler unsatisfiability proofs before full integer model construction
-/

/-
Remark: we will not define a parent structure `Cnstr` with the common
fields until the compiler provides support for avoiding the performance overhead.
-/

mutual
/-- A equality constraint and its justification/proof. -/
structure EqCnstr where
  p  : Poly
  h  : EqCnstrProof

inductive EqCnstrProof where
  | /-- An equality `a = 0` coming from the core. -/
    core0 (a : Expr) (zero : Expr)
  | /--
    An equality `a = b` coming from the core.
    `p₁` and `p₂` are the polynomials corresponding to `a` and `b`.
    -/
    core (a b : Expr) (p₁ p₂ : Poly)
  | coreNat (a b : Expr) (lhs rhs : Int.OfNat.Expr) (lhs' rhs' : Int.Linear.Expr)
  | coreToInt (a b : Expr) (toIntThm : Expr) (lhs rhs : Int.Linear.Expr)
  | /-- `e` is `p` -/
    defn (e : Expr) (p : Poly)
  | defnNat (e : Int.OfNat.Expr) (x : Var) (e' : Int.Linear.Expr)
  | norm (c : EqCnstr)
  | divCoeffs (c : EqCnstr)
  | subst (x : Var) (c₁ : EqCnstr) (c₂ : EqCnstr)
  | ofLeGe (c₁ : LeCnstr) (c₂ : LeCnstr)
  | reorder (c : EqCnstr)
  | commRingNorm (c : EqCnstr) (e : CommRing.RingExpr) (p : CommRing.Poly)
  | defnCommRing (e : Expr) (p : Poly) (re : CommRing.RingExpr) (rp : CommRing.Poly) (p' : Poly)
  | defnNatCommRing (e : Int.OfNat.Expr) (x : Var) (e' : Int.Linear.Expr) (p : Poly) (re : CommRing.RingExpr) (rp : CommRing.Poly) (p' : Poly)

/-- A divisibility constraint and its justification/proof. -/
structure DvdCnstr where
  d  : Int
  p  : Poly
  h  : DvdCnstrProof

/--
The predicate of type `Nat → Prop`, which serves as the conclusion of the
`cooper_left`, `cooper_right`, `cooper_dvd_left`, and `cooper_dvd_right` theorems.

The specific predicate used is determined as follows:
- `cooper_left_split` (if `left` is `true` and `c₃?` is `none`)
- `cooper_right_split` (if `left` is `false` and `c₃?` is `none`)
- `cooper_dvd_left_split` (if `left` is `true` and `c₃?` is `some`)
- `cooper_dvd_right_split` (if `left` is `false` and `c₃?` is `some`)

See `CooperSplit`
-/
structure CooperSplitPred where
  left     : Bool
  c₁       : LeCnstr
  c₂       : LeCnstr
  c₃?      : Option DvdCnstr

/--
An instance of the `CooperSplitPred` at `k`.
-/
structure CooperSplit where
  pred  : CooperSplitPred
  k     : Nat
  h     : CooperSplitProof

/--
The `cooper_left`, `cooper_right`, `cooper_dvd_left`, and `cooper_dvd_right` theorems have a resulting type
that is a big-or of the form `OrOver n (cooper_*_split ...)`. The predicate `(cooper_*_split ...)` has type `Nat → Prop`.
The `cutsat` procedure performs case splitting on `(cooper_*_split ... (n-1))` down to `(cooper_*_split ... 1)`.
If it derives `False` from each case, it uses `orOver_resolve` and `orOver_one` to deduce the final case,
which has type `(cooper_*_split ... 0)`.
-/
inductive CooperSplitProof where
  | /-- The first `n-1` cases are decisions (aka case-splits). -/
    dec (h : FVarId)
  | /-- The last case which has type `(cooper_*_split ... 0)` -/
    last (hs : Array (FVarId × UnsatProof)) (decVars : Array FVarId)

inductive DvdCnstrProof where
  | /-- Given `e` of the form `k ∣ p` s.t. `e = True` in the core.  -/
    core (e : Expr)
  | coreNat (e : Expr) (d : Nat) (b : Int.OfNat.Expr) (b' : Int.Linear.Expr)
  | norm (c : DvdCnstr)
  | divCoeffs (c : DvdCnstr)
  | solveCombine (c₁ c₂ : DvdCnstr)
  | solveElim (c₁ c₂ : DvdCnstr)
  | elim (c : DvdCnstr)
  | ofEq (x : Var) (c : EqCnstr)
  | subst (x : Var) (c₁ : EqCnstr) (c₂ : DvdCnstr)
  | cooper₁ (c : CooperSplit)
  /-- `c.c₃?` must be `some` -/
  | cooper₂ (c : CooperSplit)
  | reorder (c : DvdCnstr)
  | commRingNorm (c : DvdCnstr) (e : CommRing.RingExpr) (p : CommRing.Poly)

/-- An inequality constraint and its justification/proof. -/
structure LeCnstr where
  p  : Poly
  h  : LeCnstrProof

inductive LeCnstrProof where
  | core (e : Expr)
  | coreNeg (e : Expr) (p : Poly)
  | coreNat (e : Expr) (lhs rhs : Int.OfNat.Expr) (lhs' rhs' : Int.Linear.Expr)
  | coreNatNeg (e : Expr) (lhs rhs : Int.OfNat.Expr) (lhs' rhs' : Int.Linear.Expr)
  | coreToInt (e : Expr) (pos : Bool) (toIntThm : Expr) (lhs rhs : Int.Linear.Expr)
  | denoteAsIntNonneg (rhs : Int.OfNat.Expr) (rhs' : Int.Linear.Expr)
  | bound (h : Expr)
  | dec (h : FVarId)
  | norm (c : LeCnstr)
  | divCoeffs (c : LeCnstr)
  | combine (c₁ c₂ : LeCnstr)
  | combineDivCoeffs (c₁ c₂ : LeCnstr) (k : Int)
  | subst (x : Var) (c₁ : EqCnstr) (c₂ : LeCnstr)
  | ofLeDiseq (c₁ : LeCnstr) (c₂ : DiseqCnstr)
  | ofDiseqSplit (c₁ : DiseqCnstr) (decVar : FVarId) (h : UnsatProof) (decVars : Array FVarId)
  | cooper (c : CooperSplit)
  | dvdTight (c₁ : DvdCnstr) (c₂ : LeCnstr)
  | negDvdTight (c₁ : DvdCnstr) (c₂ : LeCnstr)
  | reorder (c : LeCnstr)
  | commRingNorm (c : LeCnstr) (e : CommRing.RingExpr) (p : CommRing.Poly)

/-- A disequality constraint and its justification/proof. -/
structure DiseqCnstr where
  p  : Poly
  h  : DiseqCnstrProof

inductive DiseqCnstrProof where
  | /-- An disequality `a != 0` coming from the core. That is, `(a = 0) = False` in the core. -/
    core0 (a : Expr) (zero : Expr)
  | /--
    An disequality `a ≠ b` coming from the core. That is, `(a = b) = False` in the core.
    `p₁` and `p₂` are the polynomials corresponding to `a` and `b`.
    -/
    core (a b : Expr) (p₁ p₂ : Poly)
  | coreNat (a b : Expr) (lhs rhs : Int.OfNat.Expr) (lhs' rhs' : Int.Linear.Expr)
  | coreToInt (a b : Expr) (toIntThm : Expr) (lhs rhs : Int.Linear.Expr)
  | norm (c : DiseqCnstr)
  | divCoeffs (c : DiseqCnstr)
  | neg (c : DiseqCnstr)
  | subst (x : Var) (c₁ : EqCnstr) (c₂ : DiseqCnstr)
  | reorder (c : DiseqCnstr)
  | commRingNorm (c : DiseqCnstr) (e : CommRing.RingExpr) (p : CommRing.Poly)

/--
A proof of `False`.
Remark: We will later add support for a backtracking search inside of cutsat.
-/
inductive UnsatProof where
  | dvd (c : DvdCnstr)
  | le (c : LeCnstr)
  | eq (c : EqCnstr)
  | diseq (c : DiseqCnstr)
  | cooper (c₁ c₂ : LeCnstr) (c₃ : DvdCnstr)

end

instance : Inhabited LeCnstr where
  default := { p := .num 0, h := .core default}

instance : Inhabited DvdCnstr where
  default := { d := 0, p := .num 0, h := .core default }

instance : Inhabited CooperSplitPred where
  default := { left := false, c₁ := default, c₂ := default, c₃? := none }

instance : Inhabited CooperSplit where
  default := { pred := default, k := 0, h := .dec default }

abbrev VarSet := RBTree Var compare

/-- State of the cutsat procedure. -/
structure State where
  /-- Mapping from variables to their denotations. -/
  vars : PArray Expr := {}
  /-- Mapping from `Expr` to a variable representing it. -/
  varMap  : PHashMap ExprPtr Var := {}
  /--
  `vars` before they were reordered.
  This array is empty if the variables were not reordered.
  We need them to generate the proof term because some
  justification objects contain terms using variables before the reordering.
  -/
  vars' : PArray Expr := {}
  /-- `varVap` before variables were reordered. -/
  varMap' : PHashMap ExprPtr Var := {}
  /--
  Mapping from `Nat` terms to their variable. They are also marked using `markAsCutsatTerm`.
  -/
  natVarMap : PHashMap ExprPtr Var := {}
  natVars : PArray Expr := {}
  /--
  Some `Nat` variables encode nested terms such as `b+1`.
  This is a mapping from this kind of variable to the integer variable
  representing `natCast (b+1)`.
  -/
  natDef : PHashMap ExprPtr Var := {}
  /--
  Mapping from variables to divisibility constraints. Recall that we keep the divisibility constraint in solved form.
  Thus, we have at most one divisibility per variable. -/
  dvds : PArray (Option DvdCnstr) := {}
  /--
  Mapping from variables to their "lower" bounds. We say a relational constraint `c` is a lower bound for a variable `x`
  if `x` is the maximal variable in `c`, and `x` coefficient in `c` is negative.
  -/
  lowers : PArray (PArray LeCnstr) := {}
  /--
  Mapping from variables to their "upper" bounds. We say a relational constraint `c` is a upper bound for a variable `x`
  if `x` is the maximal variable in `c`, and `x` coefficient in `c` is positive.
  -/
  uppers : PArray (PArray LeCnstr) := {}
  /--
  Mapping from variables to their disequalities. We say a disequality constraint `c` is a disequality for a variable `x`
  if `x` is the maximal variable in `c`.
  -/
  diseqs : PArray (PArray DiseqCnstr) := {}
  /--
  Mapping from variable to equation constraint used to eliminate it. `solved` variables should not occur in
  `dvdCnstrs`, `lowers`, or `uppers`.
  -/
  elimEqs : PArray (Option EqCnstr) := {}
  /--
  Elimination stack. For every variable in `elimStack`. If `x` in `elimStack`, then `elimEqs[x]` is not `none`.
  -/
  elimStack : List Var := []
  /--
  Mapping from variable to occurrences. For example, an entry `x ↦ {y, z}` means that `x` may occur in `dvdCnstrs`, `lowers`, or `uppers` of
  variables `y` and `z`.
  If `x` occurs in `dvdCnstrs[y]`, `lowers[y]`, or `uppers[y]`, then `y` is in `occurs[x]`, but the reverse is not true.
  If `x` is in `elimStack`, then `occurs[x]` is the empty set.
  -/
  occurs : PArray VarSet := {}
  /-- Partial assignment being constructed by cutsat. -/
  assignment : PArray Rat := {}
  /-- Next unique id for a constraint. -/
  nextCnstrId : Nat := 0
  /--
  `caseSplits` is `true` if cutsat is searching for model and already performed case splits.
  This information is used to decide whether a conflict should immediately close the
  current `grind` goal or not.
  -/
  caseSplits : Bool := false
  /--
  `conflict?` is `some ..` if a contradictory constraint was derived.
  This field is only set when `caseSplits` is `true`. Otherwise, we
  can convert `UnsatProof` into a Lean term and close the current `grind` goal.
  -/
  conflict? : Option UnsatProof := none
  /--
  Cache decision variables used when splitting on disequalities.
  This is necessary because the same disequality may be in different conflicts.
  -/
  diseqSplits : PHashMap Poly FVarId := {}
  /--
  Pairs `(x, n)` s.t. we have expanded the theorems
  - `Int.Linear.ediv_emod`
  - `Int.Linear.emod_nonneg`
  - `Int.Linear.emod_le`
  -/
  divMod : PHashSet (Expr × Int) := {}
  /--
  Mapping from a type `α` to its corresponding `ToIntInfo` object, which contains
  the information needed to embed `α` terms into `Int` terms.
  -/
  toIntInfos : PHashMap ExprPtr (Option ToIntInfo) := {}
  /--
  For each type `α` in `toIntInfos`, the mapping `toIntVarMap` contains a mapping
  from a α-term `e` to the pair `(toInt e, α)`.
  -/
  toIntTermMap : PHashMap ExprPtr ToIntTermInfo := {}
  /--
  `usedCommRing` is `true` if the `CommRing` has been used to normalize expressions.
  -/
  usedCommRing : Bool := false
  deriving Inhabited

end Lean.Meta.Grind.Arith.Cutsat
