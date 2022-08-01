import Lean

def f (x : Nat × Nat) :=
  match x with
  | .mk (snd := snd) .. => snd

example : f (10, 20) = 20 := rfl

open Lean
def g (e : Expr) : Expr :=
  match e with
  | .forallE (binderType := type) .. => type
  | e => e

def h (x : Nat × Nat) :=
  match x with
  | .mk (α := .(Nat)) (snd := snd) .. => snd
