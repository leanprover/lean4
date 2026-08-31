inductive Color where
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
open rbnode

inductive hiddenTree : Nat → Type
  | HR {h} (node : rbnode h Red) : hiddenTree h
  | HB {h} (node : rbnode (h+1) Black) : hiddenTree (h+1)
open hiddenTree

inductive almostNode : Nat → Type
  | LR {h cR} (left:rbnode h Red) (value:Int) (right:rbnode h cR) : almostNode h
  | RR {h cL} (left:rbnode h cL) (value:Int) (right:rbnode h Red) : almostNode h
  | V {h c} (node:rbnode h c) : almostNode h
open almostNode

def balanceRR (left : rbnode h c) (y : Int) (right : hiddenTree h) : almostNode h :=
  match h, c, left, right with
  | _, _, left, HR c => RR left y c
  | _, _, R a x b, HB c => LR (R a x b) y c
  | _, _, B a x b, HB c => V (R (B a x b) y c)
  | _, _, Leaf, HB c => V (R Leaf y c)

def balanceRR' (left : rbnode h c) (y : Int) (right : hiddenTree h) : almostNode h :=
  match h, c, right, left with
  | _, _, HR c, left => RR left y c
  | _, _, HB c, R a x b => LR (R a x b) y c
  | _, _, HB c, B a x b => V (R (B a x b) y c)
  | _, _, HB c, Leaf => V (R Leaf y c)

def balanceRR'' (left : rbnode h c) (y : Int) (right : hiddenTree h) : almostNode h :=
  match left, right with
  | left,    HR c => RR left y c
  | R a x b, HB c => LR (R a x b) y c
  | B a x b, HB c => V (R (B a x b) y c)
  | Leaf,    HB c => V (R Leaf y c)
