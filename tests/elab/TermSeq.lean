inductive TermSeq where
  | empty : TermSeq
  | cons : {α : Type} → (a : α) → (tail: TermSeq) → TermSeq

namespace TermSeq

def prodType : TermSeq → Type
  | empty => Unit
  | @cons α a tail => Prod α (prodType tail)

def asProd : (ts: TermSeq) → prodType ts
  | empty => (() : Unit)
  | @cons α a tail => (a, asProd tail)

end TermSeq
