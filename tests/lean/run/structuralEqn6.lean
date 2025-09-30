/-- The number of trailing zeros in the binary representation of `i`. -/
def trailingZeros (i : Int) : Nat :=
  if h : i = 0 then 0 else aux i.natAbs i h (Nat.le_refl _) 0
where
  aux (k : Nat) (i : Int) (hi : i ≠ 0) (hk : i.natAbs ≤ k) (acc : Nat) : Nat :=
    match k, (by omega : k ≠ 0) with
    | k + 1, _ =>
      if h : i % 2 = 0 then aux k (i / 2) (by omega) (by omega) (acc + 1)
      else acc
  termination_by structural k

/--
info: equations:
@[defeq] theorem trailingZeros.aux.eq_1 : ∀ (i : Int) (hi : i ≠ 0) (acc k_2 : Nat) (hk_2 : i.natAbs ≤ k_2 + 1),
  trailingZeros.aux k_2.succ i hi hk_2 acc = if h : i % 2 = 0 then trailingZeros.aux k_2 (i / 2) ⋯ ⋯ (acc + 1) else acc
-/
#guard_msgs in
#print equations trailingZeros.aux
