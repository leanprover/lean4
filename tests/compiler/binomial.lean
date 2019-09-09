import init.data.binomialheap

abbrev Heap := BinomialHeap Nat (fun a b => a < b)

def mkHeap (n m : Nat) : Heap :=
let hs : List Heap := n.fold (fun i hs =>
  let h : Heap := BinomialHeap.empty;
  let h : Heap := m.fold (fun j h =>
    let v := n*m - j*n - i;
    h.insert v) h;
  h :: hs)
  [];
hs.foldl (fun h₁ h₂ => h₁.merge h₂) BinomialHeap.empty

partial def display : Nat → Heap → IO Unit
| prev, h =>
  if h.isEmpty then pure ()
  else do
    let m := h.head;
    unless (prev < m) (IO.println ("failed " ++ toString prev ++ " " ++ toString m));
    display m h.tail

def main : IO Unit :=
do
let h := mkHeap 50 100;
display 0 h;
IO.println h.toList.length
