/-!
More tests related to structural indices depending on fixed parameters
-/

inductive T (n : Nat) : Nat → Type where
  | zero : T n 0
  | succ {i} : T n i  → T n (i + n) → T n i


/--
error: cannot use specified measure for structural recursion:
  its type is an inductive datatype
    T (↑f) i
  and the datatype parameter
    ↑f
  depends on the function parameter
    i
  which does not come before the varying parameters and before the indices of the recursion parameter.
-/
#guard_msgs in
def foo (i : Nat) (f : Fin i) : T f i → Unit
  | .zero => ()
  | .succ t _ => foo i f t
termination_by structural t => t

/--
error: cannot use specified measure for structural recursion:
  its type is an inductive datatype
    T (↑f) i
  and the datatype parameter
    ↑f
  depends on the function parameter
    f
  which does not come before the varying parameters and before the indices of the recursion parameter.
-/
#guard_msgs in
def bar (a : Nat) (i : Nat) (f : Fin a) : T f i → Unit
  | .zero => ()
  | .succ t _ => bar a i f t
termination_by structural t => t
