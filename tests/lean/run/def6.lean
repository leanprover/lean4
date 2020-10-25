

open Nat

inductive BV : Nat → Type
| nil  : BV 0
| cons : ∀ (n) (hd : Bool) (tl : BV n), BV (succ n)

open BV

variable (f : Bool → Bool → Bool)

def map2 : {n : Nat} →  BV n → BV n → BV n
| .(0), nil, nil             => nil
| .(n+1), cons n b1 v1, cons .(n) b2 v2 => cons n (f b1 b2) (map2 v1 v2)

theorem ex1 : map2 f nil nil = nil :=
rfl

theorem ex2 (n : Nat) (b1 b2 : Bool) (v1 v2 : BV n) : map2 f (cons n b1 v1) (cons n b2 v2) = cons n (f b1 b2) (map2 f v1 v2) :=
rfl

#print map2

def map2' : {n : Nat} →  BV n → BV n → BV n
| _, nil,          nil          => nil
| _, cons _ b1 v1, cons _ b2 v2 => cons _ (f b1 b2) (map2' v1 v2)

theorem ex3 : map2' f nil nil = nil :=
rfl

theorem ex4 (n : Nat) (b1 b2 : Bool) (v1 v2 : BV n) : map2' f (cons n b1 v1) (cons n b2 v2) = cons n (f b1 b2) (map2' f v1 v2) :=
rfl
