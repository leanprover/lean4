/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Tactic.Grind.Order.OrderM
import Lean.Meta.Tactic.Grind.Arith.Util
public section
namespace Lean.Meta.Grind.Order

def Cnstr.pp (c : Cnstr NodeId) : OrderM MessageData := do
  let u ← getExpr c.u
  let v ← getExpr c.v
  let op := match c.kind with
    | .le => "≤"
    | .lt => "<"
    | .eq => "="
  if c.k != 0 then
    return m!"{Arith.quoteIfArithTerm u} {op} {Arith.quoteIfArithTerm v} + {c.k}"
  else
    return m!"{Arith.quoteIfArithTerm u} {op} {Arith.quoteIfArithTerm v}"

def Weight.compare (a b : Weight) : Ordering :=
  if a.k < b.k then
    .lt
  else if b.k > a.k then
    .gt
  else if a.strict == b.strict then
    .eq
  else if a.strict && !b.strict then
    /-
    **Note**: Recall that we view a constraint of the
    form `x < y + k` as `x ≤ y + (k - ε)` where `ε` is
    an "infinitesimal" positive value.
    Thus, `k - ε < k`
    -/
    .lt
  else
    .gt

instance : Ord Weight where
  compare := Weight.compare

instance : LE Weight where
  le a b := compare a b ≠ .gt

instance : LT Weight where
  lt a b := compare a b = .lt

instance : DecidableLE Weight :=
  fun a b => inferInstanceAs (Decidable (compare a b ≠ .gt))

instance : DecidableLT Weight :=
  fun a b => inferInstanceAs (Decidable (compare a b = .lt))

def Weight.add (a b : Weight) : Weight :=
  { k := a.k + b.k, strict := a.strict || b.strict }

instance : Add Weight where
  add := Weight.add

def Weight.isNeg (a : Weight) : Bool :=
  a.k < 0 || (a.k == 0 && a.strict)

def Weight.isZero (a : Weight) : Bool :=
  a.k == 0 && !a.strict

end Lean.Meta.Grind.Order
