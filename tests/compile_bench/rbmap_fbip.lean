/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Sebastian Ullrich

Adapted from Appendix A.2 of "Reference Counting with Frame Limited Reuse" by Anton Lorenzen & Daan Leijen
https://www.microsoft.com/en-us/research/uploads/prod/2021/11/flreuse-tr.pdf#page=26
-/

inductive Color
  | red | black

inductive Tree where
  | leaf
  | node : Color → Tree → Nat → Bool → Tree → Tree

def fold (f : Nat → Bool → σ → σ) : Tree → σ → σ
  | .leaf,           b => b
  | .node _ l k v r, b => fold f r (f k v (fold f l b))

inductive Tree.Zipper where
  | nodeR : Color → Tree → Nat → Bool → Tree.Zipper → Tree.Zipper
  | nodeL : Color → Tree.Zipper → Nat → Bool → Tree → Tree.Zipper
  | done

def rebuild (t : Tree) : Tree.Zipper → Tree
  | .nodeR c l k v z => rebuild (.node c l k v t) z
  | .nodeL c z k v r => rebuild (.node c t k v r) z
  | .done            => t

def balance (l : Tree) (k : Nat) (v : Bool) (r : Tree) : Tree.Zipper → Tree
  | .nodeR .black l1 k1 v1 z1 => rebuild (.node .black l1 k1 v1 (.node .red l k v r)) z1
  | .nodeL .black z1 k1 v1 r1 => rebuild (.node .black (.node .red l k v r) k1 v1 r1) z1
  | .nodeR .red l1 k1 v1 z1 => match z1 with
    | .nodeR _ l2 k2 v2 z2 => balance (.node .black l2 k2 v2 l1) k1 v1 (.node .black l k v r) z2
    | .nodeL _ z2 k2 v2 r2 => balance (.node .black l1 k1 v1 l) k v (.node .black r k2 v2 r2) z2
    | .done => .node .black l1 k1 v1 (.node .red l k v r)
  | .nodeL .red z1 k1 v1 r1 => match z1 with
    | .nodeR _ l2 k2 v2 z2 => balance (.node .black l2 k2 v2 l) k v (.node .black r k1 v1 r1) z2
    | .nodeL _ z2 k2 v2 r2 => balance (.node .black l k v r) k1 v1 (.node .black r1 k2 v2 r2) z2
    | .done => .node .black (.node .red l k v r) k1 v1 r1
  | .done => .node .black l k v r

def ins (kx : Nat) (vx : Bool) (z : Tree.Zipper) : Tree → Tree
  | .leaf => balance .leaf kx vx .leaf z
  | .node c a ky vy b =>
    (if kx < ky then ins kx vx (.nodeL c z ky vy b) a
     else if kx > ky then ins kx vx (.nodeR c a ky vy z) b
     else rebuild (.node c a kx vx b) z)

def insert (k : Nat) (v : Bool) (t : Tree) : Tree :=
  ins k v .done t

def mkMapAux : Nat → Tree → Tree
  | 0,   m => m
  | n+1, m => mkMapAux n (insert n (n % 10 = 0) m)

def mkMap (n : Nat) :=
  mkMapAux n .leaf

def main (xs : List String) : IO Unit :=
  let m := mkMap xs.head!.toNat!
  let v := fold (fun _ v r => if v then r + 1 else r) m 0
  IO.println (toString v)
