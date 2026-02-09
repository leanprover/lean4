class Preorder (α : Type u) extends LE α

instance instPreorderInt : Preorder Int where

example (c x : Int) (mx : @LE.le Int instPreorderInt.toLE x c) : x ≤ c := by
  grind -order

example (c x : Int) (mx : @LE.le Int instPreorderInt.toLE (x + (-1) * c) 0) : x ≤ c := by
  grind -order

example (c x : Int) (mx : @LE.le Int instPreorderInt.toLE x c) : x ≤ c := by
  lia -order

example (c x : Int) (mx : @LE.le Int instPreorderInt.toLE (x + (-1) * c) 0) : x ≤ c := by
  lia -order
