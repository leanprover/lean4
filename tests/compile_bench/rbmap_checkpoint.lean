/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Sebastian Ullrich
-/

inductive Color
  | red | black

inductive Tree where
  | leaf
  | node : Color → Tree → Nat → Bool → Tree → Tree
  deriving Inhabited

def fold (f : Nat → Bool → σ → σ) : Tree → σ → σ
  | .leaf,           b => b
  | .node _ l k v r, b => fold f r (f k v (fold f l b))

@[inline]
def balance1 : Nat → Bool → Tree → Tree → Tree
  | kv, vv, t, .node _ (.node .red l kx vx r₁) ky vy r₂   => .node .red (.node .black l kx vx r₁) ky vy (.node .black r₂ kv vv t)
  | kv, vv, t, .node _ l₁ ky vy (.node .red l₂ kx vx r)   => .node .red (.node .black l₁ ky vy l₂) kx vx (.node .black r kv vv t)
  | kv, vv, t, .node _ l  ky vy r                         => .node .black (.node .red l ky vy r) kv vv t
  | _,  _,  _, _                                          => .leaf

@[inline]
def balance2 : Tree → Nat → Bool → Tree → Tree
  | t, kv, vv, .node _ (.node .red l kx₁ vx₁ r₁) ky vy r₂  => .node .red (.node .black t kv vv l) kx₁ vx₁ (.node .black r₁ ky vy r₂)
  | t, kv, vv, .node _ l₁ ky vy (.node .red l₂ kx₂ vx₂ r₂) => .node .red (.node .black t kv vv l₁) ky vy (.node .black l₂ kx₂ vx₂ r₂)
  | t, kv, vv, .node _ l ky vy r                           => .node .black t kv vv (.node .red l ky vy r)
  | _, _,  _,  _                                           => .leaf

def isRed : Tree → Bool
  | .node .red .. => true
  | _             => false

def ins (kx : Nat) (vx : Bool) : Tree → Tree
  | .leaf => .node .red .leaf kx vx .leaf
  | .node .red a ky vy b =>
    (if kx < ky then .node .red (ins kx vx a) ky vy b
     else if kx = ky then .node .red a kx vx b
     else .node .red a ky vy (ins kx vx b))
  | .node .black a ky vy b =>
      if kx < ky then
        (if isRed a then balance1 ky vy b (ins kx vx a)
         else .node .black (ins kx vx a) ky vy b)
      else if kx = ky then .node .black a kx vx b
      else if isRed b then balance2 a ky vy (ins kx vx b)
      else .node .black a ky vy (ins kx vx b)

def setBlack : Tree → Tree
  | .node _ l k v r   => .node .black l k v r
  | e                 => e

def insert (k : Nat) (v : Bool) (t : Tree) : Tree :=
  if isRed t then setBlack (ins k v t)
  else ins k v t

def mkMapAux (freq : Nat) : Nat → Tree → List Tree → List Tree
  | 0,   m, r => m::r
  | n+1, m, r =>
    let m := insert n (n % 10 = 0) m
    let r := if n % freq == 0 then m::r else r
    mkMapAux freq n m r

def mkMap (n : Nat) (freq : Nat) : List Tree :=
  mkMapAux freq n .leaf []

def myLen : List Tree → Nat → Nat
  | .node .. :: xs, r => myLen xs (r + 1)
  | _ :: xs,        r => myLen xs r
  | [],             r => r

def main (xs : List String) : IO Unit := do
  let [n, freq] ← pure xs | throw <| IO.userError "invalid input"
  let n     := n.toNat!
  let freq  := freq.toNat!
  let freq  := if freq == 0 then 1 else freq
  let mList := mkMap n freq
  let v     := fold (fun _ v r => if v then r + 1 else r) mList.head! 0
  IO.println s!"{myLen mList 0} {v}"
