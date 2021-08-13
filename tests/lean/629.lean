import Std.Data.BinomialHeap

open Std

def test : BinomialHeap (Nat × Nat) (λ (x, _) (y, _) => x < y) :=
  BinomialHeap.empty.insert (0, 1) |>.insert (0, 2) |>.insert (0, 3)

#eval test.head
#eval test.tail.toList
