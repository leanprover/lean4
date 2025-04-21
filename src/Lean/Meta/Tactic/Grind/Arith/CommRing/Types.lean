/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Data.PersistentArray
import Lean.Data.RBTree
import Lean.Meta.Tactic.Grind.ENodeKey
import Lean.Meta.Tactic.Grind.Arith.Util
import Lean.Meta.Tactic.Grind.Arith.CommRing.Poly

namespace Lean.Meta.Grind.Arith.CommRing
export Lean.Grind.CommRing (Var Power Mon Poly)
abbrev RingExpr := Grind.CommRing.Expr

deriving instance Repr for Power, Mon, Poly

mutual

structure EqCnstr where
  p     : Poly
  h     : EqCnstrProof
  sugar : Nat
  id    : Nat

inductive EqCnstrProof where
  | core (a b : Expr)
  | superpose (c₁ c₂ : EqCnstr)
  | simp (c₁ c₂ : EqCnstr) (k₁ k₂ : Int) (m : Mon)
  | mul (k : Int) (e : EqCnstr)
  | div (k : Int) (e : EqCnstr)

end

instance : Inhabited EqCnstrProof where
  default := .core default default

instance : Inhabited EqCnstr where
  default := { p := default, h := default, sugar := 0, id := 0 }

protected def EqCnstr.compare (c₁ c₂ : EqCnstr) : Ordering :=
  (compare c₁.sugar c₂.sugar) |>.then
  (compare c₁.p.degree c₂.p.degree) |>.then
  (compare c₁.id c₂.id)

abbrev Queue : Type := RBTree EqCnstr EqCnstr.compare

/-- State for each `CommRing` processed by this module. -/
structure Ring where
  id           : Nat
  type         : Expr
  /-- Cached `getDecLevel type` -/
  u            : Level
  /-- `CommRing` instance for `type` -/
  commRingInst : Expr
  /-- `IsCharP` instance for `type` if available. -/
  charInst?    : Option (Expr × Nat) := .none
  addFn        : Expr
  mulFn        : Expr
  subFn        : Expr
  negFn        : Expr
  powFn        : Expr
  intCastFn    : Expr
  natCastFn    : Expr
  /--
  Mapping from variables to their denotations.
  Remark each variable can be in only one ring.
  -/
  vars         : PArray Expr := {}
  /-- Mapping from `Expr` to a variable representing it. -/
  varMap       : PHashMap ENodeKey Var := {}
  /-- Mapping from Lean expressions to their representations as `RingExpr` -/
  denote       : PHashMap ENodeKey RingExpr := {}
  /-- Next unique id for `EqCnstr`s. -/
  nextId       : Nat := 0
  /-- Number of "steps": simplification and superposition. -/
  steps        : Nat := 0
  /-- Equations to process. -/
  queue        : Queue := {}
  /--
  Mapping from variables `x` to equations such that the smallest variable
  in the leading monomial is `x`.
  -/
  varToBasis   : PArray (List EqCnstr) := {}
  deriving Inhabited

/-- State for all `CommRing` types detected by `grind`. -/
structure State where
  /--
  Commutative rings.
  We expect to find a small number of rings in a given goal. Thus, using `Array` is fine here.
  -/
  rings : Array Ring := {}
  /--
  Mapping from types to its "ring id". We cache failures using `none`.
  `typeIdOf[type]` is `some id`, then `id < rings.size`. -/
  typeIdOf : PHashMap ENodeKey (Option Nat) := {}
  /- Mapping from expressions/terms to their ring ids. -/
  exprToRingId : PHashMap ENodeKey Nat := {}
  deriving Inhabited

end Lean.Meta.Grind.Arith.CommRing
