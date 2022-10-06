import Lean.Data.RBMap

open Lean

abbrev Tree : Type := RBMap Nat Bool compare

def mkMapAux : Nat → Tree → Tree
  | 0,   m => m
  | n+1, m => mkMapAux n (m.insert n (n % 10 = 0))

def mkMap (n : Nat) :=
  mkMapAux n {}

def main (xs : List String) : IO Unit :=
  let m := mkMap xs.head!.toNat!
  let v := m.fold (fun _ r v => if v then r + 1 else r) 0
  IO.println (toString v)
