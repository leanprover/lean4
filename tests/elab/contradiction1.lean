inductive MyFin : Nat → Type
  | z : MyFin (n+1)
  | s : MyFin n → MyFin (n+1)

theorem ex1 (x : MyFin 0) : False := by
  contradiction

inductive Color
| Red
| Black
open Color

inductive rbnode : Nat → Color → Type where
  | Leaf : rbnode 1 Black
  | R {h}
      (left : rbnode h Black)
      (value : Int)
      (right : rbnode h Black) : rbnode h Red
  | B {h cl cr}
      (left : rbnode h cl)
      (value : Int)
      (right : rbnode h cr) : rbnode (h+1) Black

theorem ex2 (x : rbnode 0 Color.Red) : False := by
  contradiction
