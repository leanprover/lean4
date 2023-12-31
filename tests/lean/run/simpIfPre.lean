/-!
Test support for `if-then-else` terms in the simplifier.
The condition should be simplified before trying to apply congruence.
We are currently accomplished that using pre-simp theorems.
TODO: replace them with simprocs.
In the following example, the term `g (a + <num>)` takes an
exponential amount of time to be simplified without the pre-simp theorems.
-/

def myid (x : Nat) := 0 + x

@[simp] theorem myid_eq : myid x = x := by simp [myid]

namespace Ex1
def f (x : Nat) (y z : Nat) : Nat :=
  if myid x = 0 then y else z

def g (x : Nat) : Nat :=
  match x with
  | 0 => 1
  | a+1 => f x (g a + 1) (g a)

theorem ex (h : a = 1) : g (a+32) = a := by
  simp [g, f, h]
end Ex1

namespace Ex2
def f (x : Nat) (y z : Nat) : Nat :=
  if myid x > 0 then z else y

def g (x : Nat) : Nat :=
  match x with
  | 0 => 1
  | a+1 => f x (g a + 1) (g a)

theorem ex (h : a = 1) : g (a+32) = a := by
  simp [g, f, h]
end Ex2

namespace Ex3
def f (x : Nat) (y z : Nat) : Nat :=
  if _ : myid x = 0 then y else z

def g (x : Nat) : Nat :=
  match x with
  | 0 => 1
  | a+1 => f x (g a + 1) (g a)

theorem ex (h : a = 1) : g (a+32) = a := by
  simp [g, f, h]
end Ex3

namespace Ex4
def f (x : Nat) (y z : Nat) : Nat :=
  if _ : myid x > 0 then z else y

def g (x : Nat) : Nat :=
  match x with
  | 0 => 1
  | a+1 => f x (g a + 1) (g a)

theorem ex (h : a = 1) : g (a+32) = a := by
  simp [g, f, h]
end Ex4
