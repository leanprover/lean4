theorem some_induction
  {motive : Nat → Prop}
  (zero : motive 0)
  (succ : forall n, 0 < n → let m := n - 1; motive m → motive n) :
  ∀ n, motive n
  | 0 => zero
  | n+1 => succ (n+1) (Nat.zero_lt_succ n) (some_induction zero succ n)


example (n : Nat) : n = n := by
  induction n using some_induction
  case zero => rfl
  case succ n _h _m _IH =>
    rfl

example (n : Nat) : n = n := by
  induction n using some_induction with
  | zero => rfl
  | succ n _h _m _IH =>
    rfl
