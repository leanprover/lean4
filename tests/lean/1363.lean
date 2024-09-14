import Std.Internal.Parsec
open Std Internal Parsec String

@[macro_inline] -- Error
def f : Nat → Nat
  | 0 => 0
  | n + 1 => f n

@[macro_inline] -- Error
def g : Nat → Nat
  | 0 => 0
  | n + 1 => g n
termination_by x => x

@[macro_inline] -- Error
def h : Nat → Nat → Nat
  | 0, _ => 0
  | n + 1, m => h n m
termination_by x y => x

@[macro_inline] -- Error
partial def skipMany (p : Parser α) (it : String.Iterator) : Parser PUnit := do
  match p it with
  | .success it _ => skipMany p it
  | .error _ _  => pure ()
