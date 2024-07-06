set_option linter.constructorNameAsVariable false

inductive  A (n : Nat) : Type
  | a : A n
  | b : A n → A n

/--
error: argument #3 cannot be used for structural recursion
  its type is an inductive datatype
    A n
  and parameter
    n
  depends on
    n
-/
#guard_msgs in
def A.size (acc n : Nat) : A n → Nat
  | .a => acc
  | .b a' => 1 + A.size (acc + 1) n a'
termination_by structural a => a
