/-!
Testing a few more corner cases related to structural mutual recursion, parameters, indices,
dependencies.
-/

def const (x : α) (_ : β) : α := x

private axiom test_sorry : ∀ {α}, α


inductive T (p : Nat) : (i : Nat) → Type where
  | zero : T p i
  | succ : T p i → T p (i + p) → T p i

/--
error: failed to infer structural recursion:
Cannot use parameters #4 of foo and #4 of bar:
  its type is an inductive datatype and the datatype parameter
    p1
  which cannot be fixed as it is an index or depends on an index, and indices cannot be fixed parameters when using structural recursion.
-/
#guard_msgs in
mutual
def foo (i : Nat) (p1 : Nat) (p2 : const Nat i) : T p1 i → Unit
  | .zero => ()
  | .succ t1 _ => bar i p2 p1 t1
termination_by structural t => t

def bar (i : Nat) (p2 : Nat) (p1 : const Nat p2) : T p1 i → Unit
  | .zero => ()
  | .succ t1 _ => foo i p1 p2 t1
termination_by structural t => t
end
