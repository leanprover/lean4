inductive Le (m : Nat) : Nat → Prop
  | base : Le m m
  | succ : (n : Nat) → Le m n → Le m n.succ

example : Le n n := by constructor
example : Le n m := by constructor
example : Le n n.succ := by constructor; constructor
example : Type := by constructor
