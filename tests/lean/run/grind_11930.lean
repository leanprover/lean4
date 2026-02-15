@[grind =] def f : Nat → Nat
  | 0 => 0
  | n + 1 => f n

theorem foo (n : Nat) : f n = 0 := by
  match n with
  | 0 => grind
  | n + 1 => grind [foo n]
