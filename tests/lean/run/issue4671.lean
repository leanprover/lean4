set_option linter.constructorNameAsVariable false

inductive  A (n : Nat) : Type
  | a : A n
  | b : A n → A n

/--
error: its type is an inductive datatype
  A n
and the datatype parameter
  n
depends on the function parameter
  n
which does not come before the varying parameters and before the indices of the recursion parameter.
-/
#guard_msgs in
def A.size (acc n : Nat) : A n → Nat
  | .a => acc
  | .b a' => 1 + A.size (acc + 1) n a'
termination_by structural a => a
