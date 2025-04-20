/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Data.PersistentArray
import Lean.Meta.Tactic.Grind.ENodeKey
import Lean.Meta.Tactic.Grind.Arith.Util
import Lean.Meta.Tactic.Grind.Arith.CommRing.Poly

namespace Lean.Meta.Grind.Arith.CommRing
export Lean.Grind.CommRing (Var Power Mon Poly)
abbrev RingExpr := Grind.CommRing.Expr

/-- State for each `CommRing` processed by this module. -/
structure Ring where
  type         : Expr
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
  deriving Inhabited

/-- State for all `CommRing` types detected by `grind`. -/
structure State where
  /--
  Commutative rings.
  We expect to find a small number of rings in a given goal. Thus, using `Array` is fine here.
  -/
  rings : Array Ring := {}
  /--
  Mapping from `Expr` to its "ring id". We cache failures using `none`.
  `typeIdOf[e]` is `some id`, then `id < rings.size`. -/
  typeIdOf : PHashMap ENodeKey (Option Nat) := {}
  deriving Inhabited

end Lean.Meta.Grind.Arith.CommRing
