/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
namespace Lean

/-!
  Rational numbers for implementing decision procedures.
  We should not confuse them with the Mathlib rational numbers.
-/

structure Rat where
  private mk ::
    num : Int
    den : Nat := 1
  deriving Inhabited, BEq

instance : ToString Rat where
  toString a := if a.den == 1 then toString a.num else s!"{a.num}/{a.den}"

instance : Repr Rat where
  reprPrec a _ := if a.den == 1 then repr a.num else s!"({a.num} : Rat)/{a.den}"

@[inline] def Rat.normalize (a : Rat) : Rat :=
  let n := Nat.gcd a.num.natAbs a.den
  if n == 1 then a else { num := a.num / n, den := a.den / n }

def mkRat (num : Int) (den : Nat) : Rat :=
  if den == 0 then { num := 0 } else Rat.normalize { num, den }

namespace Rat

protected def lt (a b : Rat) : Bool :=
  if a.num < 0 && b.num >= 0 then
    true
  else if a.num == 0 then
    b.num > 0
  else if a.num > 0 && b.num <= 0 then
    false
  else
    -- `a` and `b` must have the same sign
   a.num * b.den < b.num * a.den

protected def mul (a b : Rat) : Rat :=
  let g1 := Nat.gcd a.den b.num.natAbs
  let g2 := Nat.gcd a.num.natAbs b.den
  { num := (a.num / g2)*(b.num / g1)
    den := (b.den / g2)*(a.den / g1) }

protected def inv (a : Rat) : Rat :=
  if a.num < 0 then
    { num := - a.den, den := a.num.natAbs }
  else if a.num == 0 then
    a
  else
    { num := a.den, den := a.num.natAbs }

protected def div (a b : Rat) : Rat :=
  Rat.mul a b.inv

protected def add (a b : Rat) : Rat :=
  let g := Nat.gcd a.den b.den
  if g == 1 then
    { num := a.num * b.den + b.num * a.den, den := a.den * b.den }
  else
    let den := (a.den / g) * b.den
    let num := (b.den / g) * a.num + (a.den / g) * b.num
    let g1  := Nat.gcd num.natAbs g
    if g1 == 1 then
      { num, den }
    else
      { num := num / g1, den := den / g1 }

protected def sub (a b : Rat) : Rat :=
  let g := Nat.gcd a.den b.den
  if g == 1 then
    { num := a.num * b.den - b.num * a.den, den := a.den * b.den }
  else
    let den := (a.den / g) * b.den
    let num := (b.den / g) * a.num - (a.den / g) * b.num
    let g1  := Nat.gcd num.natAbs g
    if g1 == 1 then
      { num, den }
    else
      { num := num / g1, den := den / g1 }

protected def neg (a : Rat) : Rat :=
  { a with num := - a.num }

instance : LT Rat where
  lt a b := (Rat.lt a b) = true

instance (a b : Rat) : Decidable (a < b) :=
  inferInstanceAs (Decidable (_ = true))

instance : LE Rat where
  le a b := ¬(b < a)

instance (a b : Rat) : Decidable (a ≤ b) :=
  inferInstanceAs (Decidable (¬ _))

instance : Add Rat where
  add := Rat.add

instance : Sub Rat where
  sub := Rat.sub

instance : Neg Rat where
  neg := Rat.neg

instance : Mul Rat where
  mul := Rat.mul

instance : Div Rat where
  div a b := a * b.inv

instance : OfNat Rat n where
  ofNat := { num := n }

instance : Coe Int Rat where
  coe num := { num }

end Rat
end Lean
