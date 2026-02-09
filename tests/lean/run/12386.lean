def minFacAux (n : Nat) : Nat → Nat
  | k =>
    if h : n < k * k then n
    else
      if h' : k ∣ n then k
      else
        have : k ≤ n := by have := Nat.le_mul_self k; omega
        minFacAux n (k + 2)
termination_by k => n + 2 - k

def Nat.minFac (n : Nat) : Nat :=
  if 2 ∣ n then 2 else minFacAux n 3

def Nat.log (b n : Nat) : Nat :=
  if b ≤ 1 then 0 else (go b n).2 where
  go : Nat → Nat → Nat × Nat
  | _, 0 => (n, 0)
  | b, fuel + 1 =>
    if n < b then
      (n, 0)
    else
      let (q, e) := go (b * b) fuel
      if q < b then (q, 2 * e) else (q / b, 2 * e + 1)

set_option trace.Meta.Tactic true


theorem test : ¬∃ k, k ≤ Nat.log 2 15 ∧ 0 < k ∧ 15 = Nat.minFac 15 ^ k := by
  apply of_decide_eq_true
  conv => lhs; cbv
