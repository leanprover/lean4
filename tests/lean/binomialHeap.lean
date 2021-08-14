import Std

open Std
open BinomialHeap

def h₁ : BinomialHeap Nat (· < ·) := BinomialHeap.ofList _ [2, 1, 3, 5, 4]
def h₂ : BinomialHeap Nat (· < ·) := BinomialHeap.ofList _ [0, 1, 6]

#eval h₁.head
#eval h₁.tail.toList
#eval h₁.deleteMin.map (·.fst)
#eval h₁.deleteMin.map (·.snd.toList)
#eval h₁.toList
#eval h₁.toArray
#eval h₁.toArrayUnordered.qsort (· < ·)
#eval h₁.toListUnordered.toArray.qsort (· < ·)
#eval h₁.insert 7 |>.toList
#eval h₁.insert 0 |>.toList
#eval h₁.insert 4 |>.toList
#eval h₁.merge h₂ |>.toList
