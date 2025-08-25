/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Init.Core
public import Init.Grind.AC
public import Std.Data.HashMap
public import Lean.Expr
public import Lean.Data.PersistentArray
public import Lean.Meta.Tactic.Grind.ExprPtr
public section

namespace Lean.Meta.Grind.AC
open Lean.Grind.AC

structure Struct where
  id              : Nat
  type            : Expr
  /-- Cached `getLevel type` -/
  u               : Level
  op              : Expr
  neutral?        : Option Expr
  assocInst       : Expr
  idempotentInst? : Option Expr
  commInst?       : Option Expr
  neutralInst?    : Option Expr
  /--
  Mapping from variables to their denotations.
  Remark each variable can be in only one ring.
  -/
  vars             : PArray Expr := {}
  /-- Mapping from `Expr` to a variable representing it. -/
  varMap           : PHashMap ExprPtr Var := {}
  deriving Inhabited

/-- State for all associative operators detected by `grind`. -/
structure State where
  /--
  Structures/operators detected.
  We expect to find a small number of associative operators in a given goal. Thus, using `Array` is fine here.
  -/
  structs : Array Struct := {}
  /--
  Mapping from operators to its "structure id". We cache failures using `none`.
  `opIdOf[op]` is `some id`, then `id < structs.size`. -/
  opIdOf : PHashMap ExprPtr (Option Nat) := {}
  /- Mapping from expressions/terms to their structure ids. -/
  exprToStructId : PHashMap ExprPtr Nat := {}
  deriving Inhabited

end Lean.Meta.Grind.AC
