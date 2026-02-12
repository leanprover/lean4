/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Sym.ExprPtr
public import Lean.Data.PersistentHashMap
public import Lean.Data.PersistentArray
public import Init.Grind.Ring.CommSemiringAdapter
public section
namespace Lean.Meta.Sym.Arith.Ring

export Lean.Grind.CommRing (Var Power Mon Poly)
abbrev RingExpr := Grind.CommRing.Expr
/-
We use ring expressions to represent semiring expressions,
and ignore non-applicable constructors.
-/
abbrev SemiringExpr := Grind.CommRing.Expr

/-- Shared state for non-commutative and commutative semirings. -/
structure Semiring where
  id             : Nat
  type           : Expr
  /-- Cached `getDecLevel type` -/
  u              : Level
  /-- `Semiring` instance for `type` -/
  semiringInst   : Expr
  addFn?         : Option Expr := none
  mulFn?         : Option Expr := none
  powFn?         : Option Expr := none
  natCastFn?     : Option Expr := none
  /-- Mapping from Lean expressions to their representations as `SemiringExpr` -/
  denote         : PHashMap ExprPtr SemiringExpr := {}
  /--
  Mapping from variables to their denotations.
  Each variable can be in only one ring.
  -/
  vars           : PArray Expr := {}
  /-- Mapping from `Expr` to a variable representing it. -/
  varMap         : PHashMap ExprPtr Var := {}
  deriving Inhabited

/-- Shared state for non-commutative and commutative rings. -/
structure Ring where
  id             : Nat
  type           : Expr
  /-- Cached `getDecLevel type` -/
  u              : Level
  /-- `Ring` instance for `type` -/
  ringInst       : Expr
  /-- `Semiring` instance for `type` -/
  semiringInst   : Expr
  /-- `IsCharP` instance for `type` if available. -/
  charInst?      : Option (Expr × Nat)
  addFn?         : Option Expr := none
  mulFn?         : Option Expr := none
  subFn?         : Option Expr := none
  negFn?         : Option Expr := none
  powFn?         : Option Expr := none
  intCastFn?     : Option Expr := none
  natCastFn?     : Option Expr := none
  one?           : Option Expr := none
  /--
  Mapping from variables to their denotations.
  Each variable can be in only one ring.
  -/
  vars           : PArray Expr := {}
  /-- Mapping from `Expr` to a variable representing it. -/
  varMap         : PHashMap ExprPtr Var := {}
  /-- Mapping from Lean expressions to their representations as `RingExpr` -/
  denote         : PHashMap ExprPtr RingExpr := {}
  deriving Inhabited

/-- Shared state for commutative rings. -/
structure CommRing extends Ring where
  /--
  If this is a `OfSemiring.Q α` ring, this field contains the
  `semiringId` for `α`.
  -/
  semiringId?        : Option Nat
  /-- `CommSemiring` instance for `type` -/
  commSemiringInst   : Expr
  /-- `CommRing` instance for `type` -/
  commRingInst       : Expr
  /-- `NoNatZeroDivisors` instance for `type` if available. -/
  noZeroDivInst?     : Option Expr
  /-- `Field` instance for `type` if available. -/
  fieldInst?         : Option Expr
  invFn?             : Option Expr := none
  /-- `denoteEntries` is `denote` as a `PArray` for deterministic traversal. -/
  denoteEntries      : PArray (Expr × RingExpr) := {}
  deriving Inhabited

/-- Shared state for commutative semirings. -/
structure CommSemiring extends Semiring where
  /-- Id for `OfSemiring.Q` -/
  ringId             : Nat
  /-- `CommSemiring` instance for `type` -/
  commSemiringInst   : Expr
  /-- `AddRightCancel` instance for `type` if available. -/
  addRightCancelInst? : Option (Option Expr) := none
  toQFn?             : Option Expr := none
  deriving Inhabited

/-- Per-consumer ring state (e.g., for ArithNorm or grind). -/
structure State where
  rings   : Array CommRing := {}
  typeIdOf : PHashMap ExprPtr (Option Nat) := {}
  deriving Inhabited

/--
Shared ring cache, accessible from both `Sym.simp` and `grind`.
Maps types to `CommRing` templates containing synthesized instances
and lazily-computed operations (`addFn?`, etc.).
Per-context fields (`id`, `vars`, `varMap`, `denote`) are irrelevant
in the cache — each consumer resets them when copying.
-/
structure SharedRingCache where
  cache : PHashMap ExprPtr CommRing := {}
  deriving Inhabited

end Lean.Meta.Sym.Arith.Ring
