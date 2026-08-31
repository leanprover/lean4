/-
Copyright (c) 2026 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Init.Grind.Ring.CommSemiringAdapter
public import Lean.Meta.Sym.SymM
public section

namespace Lean.Meta.Sym.Arith
export Lean.Grind.CommRing (Var Power Mon Poly)
abbrev RingExpr := Grind.CommRing.Expr
/-
**Note**: recall that we use ring expressions to represent semiring expressions,
and ignore non-applicable constructors.
-/
abbrev SemiringExpr := Grind.CommRing.Expr

/-- Classification state for a type with a `Semiring` instance. -/
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
  deriving Inhabited

/-- Classification state for a type with a `Ring` instance. -/
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
  deriving Inhabited

/-- Classification state for a type with a `CommRing` instance. -/
structure CommRing extends Ring where
  /-- Inverse function if `fieldInst?` is `some inst` -/
  invFn?             : Option Expr := none
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
  deriving Inhabited

/--
Classification state for a type with a `CommSemiring` instance.
Recall that `CommSemiring` types are normalized using the `OfSemiring.Q` envelope.
-/
structure CommSemiring extends Semiring where
  /-- Id of the envelope ring `OfSemiring.Q type` -/
  ringId             : Nat
  /-- `CommSemiring` instance for `type` -/
  commSemiringInst   : Expr
  /-- `AddRightCancel` instance for `type` if available. -/
  addRightCancelInst? : Option (Option Expr) := none
  toQFn?             : Option Expr := none
  deriving Inhabited

/-- Result of classifying a type's algebraic structure. -/
inductive ClassifyResult where
  | commRing (id : Nat)
  | nonCommRing (id : Nat)
  | commSemiring (id : Nat)
  | nonCommSemiring (id : Nat)
  | /-- No algebraic structure found. -/ none
  deriving Inhabited

/-- Arith type classification state, stored as a `SymExtension`. -/
structure State where
  /-- Exponent threshold for `HPow` evaluation. -/
  exp            : Nat := 8
  /-- Commutative rings. -/
  rings          : Array CommRing := {}
  /-- Commutative semirings. -/
  semirings      : Array CommSemiring := {}
  /-- Non-commutative rings. -/
  ncRings        : Array Ring := {}
  /-- Non-commutative semirings. -/
  ncSemirings    : Array Semiring := {}
  /-- Mapping from types to their classification result. Caches failures as `.none`. -/
  typeClassify   : PHashMap ExprPtr ClassifyResult := {}
  deriving Inhabited

builtin_initialize arithExt : SymExtension State ← registerSymExtension (return {})

def getArithState : SymM State :=
  arithExt.getState

@[inline] def modifyArithState (f : State → State) : SymM Unit :=
  arithExt.modifyState f

/-- Get the exponent threshold. -/
def getExpThreshold : SymM Nat :=
  return (← getArithState).exp

/-- Set the exponent threshold. -/
def setExpThreshold (exp : Nat) : SymM Unit :=
  modifyArithState fun s => { s with exp }

/-- Run `k` with a temporary exponent threshold. -/
def withExpThreshold (exp : Nat) (k : SymM α) : SymM α := do
  let oldExp := (← getArithState).exp
  setExpThreshold exp
  try k finally setExpThreshold oldExp

end Lean.Meta.Sym.Arith
