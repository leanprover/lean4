def foo (r : Nat) : Nat :=
  match r with
  | Nat.zero => 0
  | l@(Nat.succ _) =>
    match l with
    | 0 => 0
    | Nat.succ ll =>
      match ll with
      | Nat.succ _ => 0
      | _ => 0

example {r : Nat} : foo r = 0 := by
  simp only [foo.eq_def]
  guard_target =ₛ
    (match r with
        | Nat.zero => 0
        | l@h:(Nat.succ n) =>
          match l, h with
          | 0, h => 0
          | Nat.succ ll, h =>
            match ll, h with
            | Nat.succ n_1, h => 0
            | x, h => 0) =
        0
  sorry
