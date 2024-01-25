/-!
Test that parentheses don't get in the way of structural recursion.
https://github.com/leanprover/lean4/issues/2810
-/

namespace Unary

def f (n : Nat) : Nat :=
  match n with
  | 0 => 0
  | n + 1 => (f) n

-- TODO: How can we assert that this was compiled structurally?

-- with beta-reduction
def f2 (n : Nat) : Nat :=
  match n with
  | 0 => 0
  | n + 1 => (fun n' => (f2) n') n

-- structural recursion
def f3 (n : Nat) : Nat :=
  match n with
  | 0 => 0
  | n + 1 => (f3) n
termination_by n

-- Same with rewrite

theorem f_zero (n : Nat) : f n = 0 := by
  match n with
  | .zero => rfl
  | .succ n  =>
    unfold f
    rewrite [f_zero]
    rfl

-- Same with simp

theorem f_zero' (n : Nat) : f n = 0 := by
  match n with
  | .zero => rfl
  | .succ n  =>
    unfold f
    simp only [f_zero']

end Unary

namespace Binary

def f (n m : Nat) : Nat :=
  match n with
  | 0 => 0
  | n + 1 => (f) n m

-- TODO: How can we assert that this was compiled structurally?

-- with beta-reduction
def f2 (n m : Nat) : Nat :=
  match n with
  | 0 => 0
  | n + 1 => (fun n' => (f2) n' m) n

-- structural recursion
def f3 (n m : Nat) : Nat :=
  match n with
  | 0 => 0
  | n + 1 => (f3) n m
termination_by n

-- Same with rewrite

theorem f_zero (n m : Nat) : f n m = 0 := by
  match n with
  | .zero => rfl
  | .succ n  =>
    unfold f
    rewrite [f_zero]
    rfl

-- Same with simp

theorem f_zero' (n m : Nat) : f n m = 0 := by
  match n with
  | .zero => rfl
  | .succ n  =>
    unfold f
    simp only [f_zero']

end Binary
