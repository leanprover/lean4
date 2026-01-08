/-
Additional tests for #11745: nonstandard instances in grind and simp +arith
These extend the basic tests in grind_11745.lean
-/

-- Setup: non-canonical LE and LT instances via class extension
class Preorder (α : Type u) extends LE α
class StrictPreorder (α : Type u) extends LT α

instance instPreorderInt : Preorder Int where
instance instStrictPreorderInt : StrictPreorder Int where
instance instPreorderNat : Preorder Nat where
instance instStrictPreorderNat : StrictPreorder Nat where

-- LT instances (Int)
example (x y : Int) (h : @LT.lt Int instStrictPreorderInt.toLT x y) : x < y := by
  grind -order

example (x y : Int) (h : @LT.lt Int instStrictPreorderInt.toLT x y) : x < y := by
  lia -order

-- Nat LE instances
example (x y : Nat) (h : @LE.le Nat instPreorderNat.toLE x y) : x ≤ y := by
  grind -order

example (x y : Nat) (h : @LE.le Nat instPreorderNat.toLE x y) : x ≤ y := by
  lia -order

-- Nat LT instances
example (x y : Nat) (h : @LT.lt Nat instStrictPreorderNat.toLT x y) : x < y := by
  grind -order

example (x y : Nat) (h : @LT.lt Nat instStrictPreorderNat.toLT x y) : x < y := by
  lia -order

-- Mixed canonical and non-canonical instances
example (x y z : Int)
    (h1 : @LE.le Int instPreorderInt.toLE x y)  -- non-canonical
    (h2 : y ≤ z)                                -- canonical
    : x ≤ z := by
  grind -order

example (x y z : Int)
    (h1 : @LE.le Int instPreorderInt.toLE x y)
    (h2 : y ≤ z)
    : x ≤ z := by
  lia -order

-- Equality derived from two LE constraints
example (x y : Int)
    (h1 : @LE.le Int instPreorderInt.toLE x y)
    (h2 : @LE.le Int instPreorderInt.toLE y x)
    : x = y := by
  grind -order

example (x y : Int)
    (h1 : @LE.le Int instPreorderInt.toLE x y)
    (h2 : @LE.le Int instPreorderInt.toLE y x)
    : x = y := by
  lia -order

-- simp +arith with non-canonical instances
example (c x : Int) (mx : @LE.le Int instPreorderInt.toLE x c) : x ≤ c := by
  simp +arith [mx]

example (c x : Int) (mx : @LT.lt Int instStrictPreorderInt.toLT x c) : x < c := by
  simp +arith [mx]

example (c x : Nat) (mx : @LE.le Nat instPreorderNat.toLE x c) : x ≤ c := by
  simp +arith [mx]
