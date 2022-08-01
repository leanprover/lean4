import Lean.Data.Parsec
open Lean Parsec

@[macroInline] -- Error
def f : Nat → Nat
  | 0 => 0
  | n + 1 => f n

@[macroInline] -- Error
def g : Nat → Nat
  | 0 => 0
  | n + 1 => g n
termination_by g x => x

@[macroInline] -- Error
def h : Nat → Nat → Nat
  | 0, _ => 0
  | n + 1, m => h n m
termination_by h x y => x

@[macroInline] -- Error
partial def skipMany (p : Parsec α) (it : String.Iterator) : Parsec PUnit := do
  match p it with
  | .success it _ => skipMany p it
  | .error _ _  => pure ()
