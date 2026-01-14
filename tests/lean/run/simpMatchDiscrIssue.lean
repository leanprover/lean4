/-!
Test support for `match`-applications in the simplifier.
The discriminants should be simplified before trying to apply congruence.
In the following example, the term `g (a + <num>)` takes an
exponential amount of time to be simplified the discriminants are not simplified,
and the `match`-application reduced before visiting the alternatives.
-/

def myid (x : Nat) := 0 + x

@[simp] theorem myid_eq : myid x = x := by simp [myid]

def f (x : Nat) (y z : Nat) : Nat :=
  match myid x with
  | 0   => y
  | _+1 => z

def g (x : Nat) : Nat :=
  match x with
  | 0 => 1
  | a+1 => f x (g a + 1) (g a)

theorem ex (h : a = 1) : g (a+64) = a := by
  simp [g, f, h]
