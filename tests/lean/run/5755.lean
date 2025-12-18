inductive C : Type where
| C1 (b     : Bool) : C
| C2 (c1 c2 : C)    : C
deriving Inhabited

open C

def id1 (b : Bool) : C := C1 b

def id2 (c : C) : C :=
  match c with
  | C1 b     => id1 b
  | C2 c1 c2 => C2 (id2 c1) (id2 c2)

theorem id2_is_idempotent : id2 (id2 c) ≠ id2 c :=
  match c with
  | C1 b  =>  by
    guard_target =ₛ  id2 (id2 (C1 b)) ≠ id2 (C1 b)
    dsimp only [id2]
    guard_target =ₛ  id2 (id1 b) ≠ id1 b
    sorry
  | C2 _ _ => by
    sorry

example : id2 (id1 b) ≠ a := by
  fail_if_success dsimp only [id2]
  dsimp only [id2, id1]
  guard_target =ₛ  C1 b ≠ a
  sorry


/-
Here is another problematic example that has been fixed.
-/


def f : Nat → Nat
  | 0 => 1
  | x+1 => 2 * f x

def fib : Nat → Nat
  | 0 => 1
  | 1 => 1
  | x+2 => fib (x+1) + fib x

example : 0 + f (fib 10000) = a := by
  simp [f] -- should not trigger max rec depth
  guard_target =ₛ  f (fib 10000) = a
  sorry
