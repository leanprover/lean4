def f (x : Nat) :=
  open Nat in
  succ (succ x)

theorem f_eq : f x = Nat.succ (Nat.succ x) :=
  rfl

def g (x : Nat) := open Nat in succ (succ x)

theorem f_eq_g : f x = g x := rfl

def h (x : Nat) := Nat.succ (open Nat in succ x)

theorem f_eq_h : f x = h x := rfl

open Nat in
def h' (x : Nat) := succ x

theorem ex (x y : Nat) (h : x = y) : x + 1 = y + 1 := by
  open Nat in show succ x = succ y
  apply congrArg
  assumption


inductive InductiveWithAVeryLongName where
  | c1 | c2 | c3 | c4 | c5 | c6 | c7

def foo (e : InductiveWithAVeryLongName) : Type :=
  open InductiveWithAVeryLongName in
  match e with
    | c1 => Nat
    | c2 => Nat → Nat
    | c3 => Nat → Nat → Nat
    | c4 => Nat → Nat → Nat → Nat
    | c5 => Nat → Nat → Nat → Nat → Nat
    | c6 => Nat → Nat → Nat → Nat → Nat → Nat
    | c7 => Nat → Nat → Nat → Nat → Nat → Nat → Nat
