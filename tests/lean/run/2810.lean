/-!
Test that parentheses don't get in the way of structural recursion.
https://github.com/leanprover/lean4/issues/2810
-/

def f (n : Nat) : Nat :=
  match n with
  | 0 => 0
  | n + 1 => (f) n

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
termination_by f3 n => n

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
