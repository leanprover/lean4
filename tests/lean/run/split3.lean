def g (xs ys : List Nat) : Nat :=
  match xs, ys with
  | [a, b], _ => Nat.succ (a+b)
  | _, [b, c] => Nat.succ b
  | _, _   => 1

example (a b : Bool) (x y z : Nat) (xs : List Nat) (h1 : (if a then x else y) = 0) (h2 : xs.head! = 0) : g [x] xs = 1 := by
  simp [g]
  repeat any_goals (split at *)
  any_goals (first | decide | contradiction | injections)
  next b c _ _ _ =>
    show Nat.succ b = 1
    subst xs; simp [List.head!] at h2; simp [h2]
  next b c _ _ _ =>
    show Nat.succ b = 1
    subst xs; simp [List.head!] at h2; simp [h2]

example (a : Bool) (h1 : (if a then x else y) = 1) : x + y > 0 := by
  split at h1
  . subst h1; rw [Nat.succ_add]; apply Nat.zero_lt_succ
  . subst h1; apply Nat.zero_lt_succ

def f (x : Nat) : Nat :=
  match x with
  | 100 => 0
  | 200 => 0
  | _   => 1

example (h1 : f x = 0) (h2 : x > 300) : False := by
  simp [f] at h1
  split at h1
  . contradiction
  . contradiction
  . contradiction

example (h1 : f x = 0) (h2 : x > 300) : False := by
  simp [f] at h1
  split at h1 <;> contradiction
