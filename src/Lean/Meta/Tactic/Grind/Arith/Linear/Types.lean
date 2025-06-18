/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Std.Internal.Rat
import Init.Grind.Ring.Poly
import Init.Grind.Ordered.Linarith
import Lean.Data.PersistentArray
import Lean.Meta.Tactic.Grind.ExprPtr

namespace Lean.Meta.Grind.Arith.Linear
export Lean.Grind.Linarith (Var Poly)
export Std.Internal (Rat)
abbrev LinExpr := Lean.Grind.Linarith.Expr

deriving instance Hashable for Poly
deriving instance Hashable for Grind.Linarith.Expr

mutual
/-- An equality constraint and its justification/proof. -/
structure EqCnstr where
  p      : Poly
  h      : EqCnstrProof

inductive EqCnstrProof where
  | core (a b : Expr) (lhs rhs : LinExpr)
  | coreCommRing (a b : Expr) (ra rb : Grind.CommRing.Expr) (p : Grind.CommRing.Poly) (lhs' : LinExpr)
  | neg (c : EqCnstr)
  | coeff (k : Nat) (c : EqCnstr)
  | subst (x : Var) (c₁ : EqCnstr) (c₂ : EqCnstr)

/-- An inequality constraint and its justification/proof. -/
structure IneqCnstr where
  p      : Poly
  strict : Bool
  h      : IneqCnstrProof

inductive IneqCnstrProof where
  | core (e : Expr) (lhs rhs : LinExpr)
  | notCore (e : Expr) (lhs rhs : LinExpr)
  | coreCommRing (e : Expr) (lhs rhs : Grind.CommRing.Expr) (p : Grind.CommRing.Poly) (lhs' : LinExpr)
  | notCoreCommRing (e : Expr) (lhs rhs : Grind.CommRing.Expr) (p : Grind.CommRing.Poly) (lhs' : LinExpr)
  | combine (c₁ : IneqCnstr) (c₂ : IneqCnstr)
  | norm (c₁ : IneqCnstr) (k : Nat)
  | dec (h : FVarId)
  | ofDiseqSplit (c₁ : DiseqCnstr) (decVar : FVarId) (h : UnsatProof) (decVars : Array FVarId)
  | oneGtZero
  | /-- `a ≤ b` from an equality `a = b` coming from the core. -/
    ofEq (a b : Expr) (la lb : LinExpr)
  | /-- `a ≤ b` from an equality `a = b` coming from the core. -/
    ofCommRingEq (a b : Expr) (ra rb : Grind.CommRing.Expr) (p : Grind.CommRing.Poly) (lhs' : LinExpr)
  | subst (x : Var) (c₁ : EqCnstr) (c₂ : IneqCnstr)

structure DiseqCnstr where
  p  : Poly
  h  : DiseqCnstrProof

inductive DiseqCnstrProof where
  | core (a b : Expr) (lhs rhs : LinExpr)
  | coreCommRing (a b : Expr) (ra rb : Grind.CommRing.Expr) (p : Grind.CommRing.Poly) (lhs' : LinExpr)
  | neg (c : DiseqCnstr)
  | subst (k₁ k₂ : Int) (c₁ : EqCnstr) (c₂ : DiseqCnstr)
  | subst1 (k : Int) (c₁ : EqCnstr) (c₂ : DiseqCnstr)
  | oneNeZero

inductive UnsatProof where
  | diseq (c : DiseqCnstr)
  | lt (c : IneqCnstr)

end

instance : Inhabited DiseqCnstr where
  default := { p := .nil, h := .core default default .zero .zero }

instance : Inhabited EqCnstr where
  default := { p := .nil, h := .core default default .zero .zero }

abbrev VarSet := RBTree Var compare

/--
State for each algebraic structure by this module.
Each type must at least implement the instance `IntModule`.
For being able to process inequalities, it must at least implement `Preorder`, and `IntModule.IsOrdered`
-/
structure Struct where
  id               : Nat
  /-- If the structure is a ring, we store its id in the `CommRing` module at `ringId?` -/
  ringId?          : Option Nat
  type             : Expr
  /-- Cached `getDecLevel type` -/
  u                : Level
  /-- `IntModule` instance -/
  intModuleInst    : Expr
  /-- `Preorder` instance if available -/
  preorderInst?    : Option Expr
  /-- `IntModule.IsOrdered` instance with `Preorder` if available -/
  isOrdInst?       : Option Expr
  /-- `PartialOrder` instance if available -/
  partialInst?     : Option Expr
  /-- `LinearOrder` instance if available -/
  linearInst?      : Option Expr
  /-- `NoNatZeroDivisors` -/
  noNatDivInst?    : Option Expr
  /-- `Ring` instance -/
  ringInst?        : Option Expr
  /-- `CommRing` instance -/
  commRingInst?    : Option Expr
  /-- `Ring.IsOrdered` instance with `Preorder` -/
  ringIsOrdInst?   : Option Expr
  /-- `Field` instance -/
  fieldInst?       : Option Expr
  /-- `IsCharP` instance for `type` if available. -/
  charInst?        : Option (Expr × Nat)
  zero             : Expr
  ofNatZero        : Expr
  one?             : Option Expr
  leFn?            : Option Expr
  ltFn?            : Option Expr
  addFn            : Expr
  hmulFn           : Expr
  hmulNatFn        : Expr
  hsmulFn?         : Option Expr
  hsmulNatFn?      : Option Expr
  subFn            : Expr
  negFn            : Expr
  /--
  Mapping from variables to their denotations.
  Remark each variable can be in only one ring.
  -/
  vars             : PArray Expr := {}
  /-- Mapping from `Expr` to a variable representing it. -/
  varMap           : PHashMap ExprPtr Var := {}
  /--
  Mapping from variables to their "lower" bounds. We say a relational constraint `c` is a lower bound for a variable `x`
  if `x` is the maximal variable in `c`, and `x` coefficient in `c` is negative.
  -/
  lowers : PArray (PArray IneqCnstr) := {}
  /--
  Mapping from variables to their "upper" bounds. We say a relational constraint `c` is a upper bound for a variable `x`
  if `x` is the maximal variable in `c`, and `x` coefficient in `c` is positive.
  -/
  uppers : PArray (PArray IneqCnstr) := {}
  /--
  Mapping from variables to their disequalities. We say a disequality constraint `c` is a disequality for a variable `x`
  if `x` is the maximal variable in `c`.
  -/
  diseqs : PArray (PArray DiseqCnstr) := {}
  /-- Partial assignment being constructed by linarith. -/
  assignment : PArray Rat := {}
  /--
  `caseSplits` is `true` if linarith is searching for model and already performed case splits.
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
  Mapping from variable to equation constraint used to eliminate it. `solved` variables should not occur in
  `diseqs`, `lowers`, or `uppers`.
  -/
  elimEqs : PArray (Option EqCnstr) := {}
  /--
  Elimination stack. For every variable in `elimStack`. If `x` in `elimStack`, then `elimEqs[x]` is not `none`.
  -/
  elimStack : List Var := []
  /--
  Mapping from variable to occurrences.
  For example, an entry `x ↦ {y, z}` means that `x` may occur in `lowers`, or `uppers`, or `diseqs` of
  variables `y` and `z`.
  If `x` occurs in `diseqs[y]`, `lowers[y]`, or `uppers[y]`, then `y` is in `occurs[x]`,
  but the reverse is not true.
  If `x` is in `elimStack`, then `occurs[x]` is the empty set.
  -/
  occurs : PArray VarSet := {}
  /--
  Linear constraints that are not supported.
  We use this information for diagnostics.
  TODO: store constraints instead.
  -/
  ignored : PArray Expr := {}
  deriving Inhabited

/-- State for all `IntModule` types detected by `grind`. -/
structure State where
  /--
  Structures detected.
  We expect to find a small number of `IntModule`s in a given goal. Thus, using `Array` is fine here.
  -/
  structs : Array Struct := {}
  /--
  Mapping from types to its "structure id". We cache failures using `none`.
  `typeIdOf[type]` is `some id`, then `id < structs.size`. -/
  typeIdOf : PHashMap ExprPtr (Option Nat) := {}
  /- Mapping from expressions/terms to their structure ids. -/
  exprToStructId : PHashMap ExprPtr Nat := {}
  deriving Inhabited

end Lean.Meta.Grind.Arith.Linear
