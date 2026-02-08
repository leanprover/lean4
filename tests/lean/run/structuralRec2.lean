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
  which is not fixed.
-/
#guard_msgs in
def foo (i : Nat) (f : Fin i) : T f i → Unit
  | .zero => ()
  | .succ t _ => foo i f t
termination_by structural t => t

def bar (a : Nat) (i : Nat) (f : Fin a) : T f i → Unit
  | .zero => ()
  | .succ t _ => bar a i f t
termination_by structural t => t

/--
info: bar.induct (a : Nat) (f : Fin a) (motive : (i : Nat) → T (↑f) i → Prop) (case1 : motive 0 T.zero)
  (case2 : ∀ (i : Nat) (t : T (↑f) i) (a_1 : T (↑f) (i + ↑f)), motive i t → motive i (t.succ a_1)) (i : Nat)
  (a✝ : T (↑f) i) : motive i a✝
-/
#guard_msgs in
#check bar.induct
