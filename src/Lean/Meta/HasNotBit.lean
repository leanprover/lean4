/-
Copyright (c) 2023 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joachim Breitner
-/

module
prelude
public import Lean.Meta.Basic
import Lean.Meta.MatchUtil

/-!
Utility functions around `Nat.hasNotBit`, used by sparse cases.
-/

open Lean Meta

public def mkHasNotBit (e : Expr) (ns : Array Nat) : Expr := Id.run do
  let mut mask := 0
  for n in ns do
    mask := mask ||| (1 <<< n)
  return mkApp2 (mkConst `Nat.hasNotBit) (mkRawNatLit mask) e

public def mkHasNotBitProof (e : Expr) (ns : Array Nat) : MetaM Expr := do
  /-
  In theory, it should suffice to write
     mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Nat) (mkNatLit 0)
  (which would be nice and simple and would not need arguments)
  but somehow that does not trigger the kernel's `reduce_nat` code path, even with `eagerReduce`.

  It works to use `Nat.ne_of_beq_eq_false`, though:
  -/
  let some (_, lhs, rhs) ← matchNe? (mkHasNotBit e ns) | unreachable!
  return mkApp3 (mkConst ``Nat.ne_of_beq_eq_false)
    lhs rhs (mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Bool) (mkConst ``Bool.false))

public def isHasNotBit? (e : Expr) : Option Expr :=
  match_expr e with
  | Nat.hasNotBit _mask e' => some e'
  | _                      => none

/--
Is `e` a `hasNotBit` type that can be refuted?
Then return an expression that's the negation of it.
(This is used by `contradiction`)
-/
public def refutableHasNotBit? (e : Expr) : MetaM (Option Expr) := do
  match_expr e with
  | Nat.hasNotBit mask bit =>
    let bit' ← whnf bit -- reduce ctorIdxApp, to get closed terms
    if bit'.hasFVar then return none
    -- Reduce to get equalities
    let some (_, lhs, rhs) ← matchNe? (mkApp2 (mkConst `Nat.hasNotBit) mask bit') | unreachable!
    if (← isDefEq lhs rhs) then
      return some <| mkApp3 (mkConst ``Nat.eq_of_beq_eq_true) lhs rhs reflBoolTrue
    else
      return none
  | _ => return none
