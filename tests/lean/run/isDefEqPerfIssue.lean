def g (n : Nat) (a : Array α) (i j : Fin a.size) : Array α :=
  match n with
  | 0   => a.swap i j
  | n+1 => g n a j i

partial def f (i : Nat) (a : Array α) : Array α :=
  if h : i < a.size then
    let a' := g 100 a ⟨i, h⟩ ⟨i - Nat.zero.succ, by exact Nat.lt_of_le_of_lt (Nat.pred_le i) h⟩
    have : a'.size - i >= 0 := sorry
    f (i+1) a'
  else
    a
