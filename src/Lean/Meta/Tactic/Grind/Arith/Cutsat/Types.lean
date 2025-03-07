/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Data.Int.Linear
import Std.Internal.Rat
import Lean.Data.PersistentArray
import Lean.Meta.Tactic.Grind.ENodeKey
import Lean.Meta.Tactic.Grind.Arith.Util

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
  | expr (h : Expr)
  | core (p₁ p₂ : Poly) (h : Expr)
  | norm (c : EqCnstr)
  | divCoeffs (c : EqCnstr)
  | subst (x : Var) (c₁ : EqCnstr) (c₂ : EqCnstr)
  | ofLeGe (c₁ : LeCnstr) (c₂ : LeCnstr)

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
  | expr (h : Expr)
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

/-- An inequalirty constraint and its justification/proof. -/
structure LeCnstr where
  p  : Poly
  h  : LeCnstrProof

inductive LeCnstrProof where
  | expr (h : Expr)
  | notExpr (p : Poly) (h : Expr)
  | norm (c : LeCnstr)
  | divCoeffs (c : LeCnstr)
  | combine (c₁ c₂ : LeCnstr)
  | combineDivCoeffs (c₁ c₂ : LeCnstr) (k : Int)
  | subst (x : Var) (c₁ : EqCnstr) (c₂ : LeCnstr)
  | ofLeDiseq (c₁ : LeCnstr) (c₂ : DiseqCnstr)
  | ofDiseqSplit (c₁ : DiseqCnstr) (decVar : FVarId) (h : UnsatProof) (decVars : Array FVarId)
  | cooper (c : CooperSplit)

  -- TODO: missing constructors

/-- A disequality constraint and its justification/proof. -/
structure DiseqCnstr where
  p  : Poly
  h  : DiseqCnstrProof

inductive DiseqCnstrProof where
  | expr (h : Expr)
  | core (p₁ p₂ : Poly) (h : Expr)
  | norm (c : DiseqCnstr)
  | divCoeffs (c : DiseqCnstr)
  | neg (c : DiseqCnstr)
  | subst (x : Var) (c₁ : EqCnstr) (c₂ : DiseqCnstr)

/--
A proof of `False`.
Remark: We will later add support for a backtraking search inside of cutsat.
-/
inductive UnsatProof where
  | dvd (c : DvdCnstr)
  | le (c : LeCnstr)
  | eq (c : EqCnstr)
  | diseq (c : DiseqCnstr)
  | cooper (c₁ c₂ : LeCnstr) (c₃ : DvdCnstr)

end

instance : Inhabited LeCnstr where
  default := { p := .num 0, h := .expr default }

instance : Inhabited DvdCnstr where
  default := { d := 0, p := .num 0, h := .expr default }

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
  varMap  : PHashMap ENodeKey Var := {}
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
  Mapping from terms (e.g., `x + 2*y + 2`, `3*x`, `5`) to polynomials representing them.
  These are terms used to propagate equalities between this module and the congruence closure module.
  -/
  terms : PHashMap ENodeKey Poly := {}
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
  /- TODO: Model-based theory combination. -/
  deriving Inhabited

end Lean.Meta.Grind.Arith.Cutsat
