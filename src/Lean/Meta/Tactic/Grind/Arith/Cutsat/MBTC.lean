/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Tactic.Grind.Arith.Cutsat.Util
import Lean.Meta.Tactic.Grind.MBTC
import Lean.Meta.Tactic.Grind.Arith.ModelUtil
import Lean.Meta.Tactic.Grind.Arith.Cutsat.Model
public section
namespace Lean.Meta.Grind.Arith.Cutsat

private def isSignedType (α : Expr) : Bool :=
  α.isConstOf ``Int8 || α.isConstOf ``Int16 || α.isConstOf ``Int32 || α.isConstOf ``Int64

/--
Returns the modulus of the embedded type `α` (`n` for `Fin n`, `2^w` for the fixed-width
types) if it is known. Numerals of embedded types with known modulus are not given
embedding-accessor applications: their embedded value is computed directly (e.g., during
model-based theory combination).
-/
def modulus? (α : Expr) : GoalM (Option Nat) := do
  match_expr α with
  | Fin n => getNatValue? n
  | BitVec w =>
    let some w ← getNatValue? w | return none
    return some (2 ^ w)
  | UInt8 => return some (2 ^ 8)
  | UInt16 => return some (2 ^ 16)
  | UInt32 => return some (2 ^ 32)
  | UInt64 => return some (2 ^ 64)
  | Int8 => return some (2 ^ 8)
  | Int16 => return some (2 ^ 16)
  | Int32 => return some (2 ^ 32)
  | Int64 => return some (2 ^ 64)
  | _ => return none -- `USize`/`ISize`: platform-dependent width

/--
Returns the embedded (`Fin.val`/`toNat`/`toInt`) value of a numeral of an embedded type
(e.g., `(2 : Fin 3) ↦ 2`, `(-1 : Fin 4) ↦ 3`, `(200 : Int8) ↦ -56`). Numerals have no
embedding-accessor application in the E-graph, so their value is computed directly.
-/
private def getEmbeddedLitValue? (e : Expr) : GoalM (Option Rat) := do
  let value? (α k : Expr) (neg : Bool) : GoalM (Option Rat) := do
    let some k ← getNatValue? k | return none
    let some m ← modulus? α | return none
    let m : Int := m
    let k : Int := if neg then -(k : Int) else (k : Int)
    let v := k % m
    let v := if isSignedType α && v ≥ m / 2 then v - m else v
    return some (v : Rat)
  match_expr e with
  | OfNat.ofNat α k _ => value? α k false
  | Neg.neg α _ a =>
    let_expr OfNat.ofNat _ k _ := a | return none
    value? α k true
  | _ => return none

private partial def getAssignmentExt? (e : Expr) : GoalM (Option Rat) := do
  if let some val ← getEmbeddedLitValue? e then
    return some val
  if let some val ← getAssignment? (← get) e then
    -- Easy case when `e : Int`
    return some val
  /-
  **Note**: The following code assumes that instantiated mvars occurring in types
  have been instantiated.
  -/
  let type ← inferType e
  if type == Int.mkType then
    -- It should have been handled in the previous getAssignment?
    return none
  else if type == Nat.mkType then
    -- TODO: improve this case.
    for parent in (← getParents e).elems do
      let_expr NatCast.natCast _ inst _ := parent | pure ()
      let_expr instNatCastInt := inst | pure ()
      return (← getAssignment? (← get) parent)
  else
    -- `e` is a term of an embedded type (e.g., `Fin`, `BitVec`, `UInt8`): use the value of an
    -- embedding application of `e` among its parents. Chains such as `a.toBitVec.toNat` are
    -- resolved one step at a time; only the last step is a cutsat (`Nat`/`Int`) term.
    for parent in (← getParents (← getRoot e)).elems do
      if let some a := embeddingArg? parent then
        if (← isEqv a e) then
          if let some v ← getAssignmentExt? (← getRoot parent) then
            return some v
  return none

/--
Returns the value of `e` in cutsat's current *candidate* assignment if that value is an
integer. `e` may be an `Int` term, or a `Nat` term whose cast to `Int` has been
internalized by cutsat. The result is a heuristic, not a guarantee: the assignment may
contain rational or default values (e.g. from eliminated or skipped variables), in which
case it is not a model of the integer constraints; such values are filtered per term.
This is sufficient for model-based theory combination, which only uses the values to
propose case splits. The homomorphism engine is the intended client: all homomorphism
target domains are handled by cutsat, so the result type is `Int`.
-/
def getModelValue? (e : Expr) : GoalM (Option Int) := do
  let some v ← getAssignmentExt? e | return none
  unless v.den == 1 do return none
  return some v.num

private def hasTheoryVar (e : Expr) : GoalM Bool := do
  cutsatExt.hasTermAtRoot e

/-
**Note**: cutsat is a procedure for linear integer arithmetic. Thus, morally a
nonlinear multiplication, division, and modulo are **not** interpreted by cutsat.
Thus, we enable model-theory combination for them. This is necessary for examples
such as:
```
example {a b : Nat} (ha : 1 ≤ a) : (a - 1 + 1) * b = a * b := by grind
```
Note that we currently use a restrictive/cheaper version of mbtc. We only case-split
on `a = b`, if they have the same assignment **and** occur as the `i`-th argument of
the same function symbol. The latter reduces the number of case-splits we have to
perform, but misses the following variant of the problem above.
```
example {a b : Nat} (ha : 1 ≤ a) : (a - 1 + 1) * b = b * a := by grind
```
If this becomes an issue in practice, we can add a flag for enabling the more
expensive version of `mbtc`.
-/

private def isNonlinearTerm (e : Expr) : GoalM Bool :=
  match_expr e with
  | HMul.hMul _ _ _ _ a b => return (← getIntValue? a <|> getIntValue? b).isNone
  | HDiv.hDiv _ _ _ _ _ b => return (← getIntValue? b).isNone
  | HMod.hMod _ _ _ _ _ b => return (← getIntValue? b).isNone
  | _ => return false

private def isInterpreted (e : Expr) : GoalM Bool := do
  if isInterpretedTerm e then
    return !(← isNonlinearTerm e)
  let f := e.getAppFn
  /-
  **Note**: `grind` normalizes terms, but some of them cannot be rewritten by `simp` because
  the rewrite would produce a type incorrect term. Thus, we may have `LT.lt` applications in
  the goal.
  -/
  return f.isConstOf ``LE.le || f.isConstOf ``Dvd.dvd || f.isConstOf ``LT.lt

private def eqAssignment (a b : Expr) : GoalM Bool := do
  let some v₁ ← getAssignmentExt? a | return false
  let some v₂ ← getAssignmentExt? b | return false
  return v₁ == v₂

def mbtc : GoalM Bool := do
  Grind.mbtc {
    hasTheoryVar := hasTheoryVar
    isInterpreted := isInterpreted
    eqAssignment := eqAssignment
  }

end Lean.Meta.Grind.Arith.Cutsat
