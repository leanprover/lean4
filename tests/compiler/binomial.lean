import Std.Data.BinomialHeap

open Std

abbrev Heap := BinomialHeap Nat (fun a b => a < b)

def mkHeap (n m : Nat) : Heap :=
let hs : List Heap := n.fold (fun i hs =>
  let h : Heap := BinomialHeap.empty
  let h : Heap := m.fold (fun j h =>
    let v := n*m - j*n - i
    h.insert v) h
  h :: hs)
  []
hs.foldl (fun h₁ h₂ => h₁.merge h₂) BinomialHeap.empty

partial def display : Nat → Heap → IO Unit
| prev, h => do
  if h.isEmpty then pure ()
  else
    let m := h.head
    unless prev < m do IO.println s!"failed {prev} {m}"
    display m h.tail

def main : IO Unit := do
let h := mkHeap 20 20
display 0 h
IO.println h.toList.length
