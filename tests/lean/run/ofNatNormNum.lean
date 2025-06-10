class OfNatSound (α : Type u) [Add α] [(n : Nat) → OfNat α n] : Prop where
  ofNat_add (n m : Nat) : (OfNat.ofNat n : α) + OfNat.ofNat m = OfNat.ofNat (n+m)

export OfNatSound (ofNat_add)

theorem ex1 {α : Type u} [Add α] [(n : Nat) → OfNat α n] [OfNatSound α] : (10000000 : α) + 10000000 = 20000000 :=
  ofNat_add ..

-- Some example structure
class S (α : Type u) extends Add α, Mul α, Zero α, One α where
  add_assoc (a b c : α)    : a + b + c = a + (b + c)
  add_zero (a : α)         : a + 0 = a
  zero_add (a : α)         : 0 + a = a
  mul_zero (a : α)         : a * 0 = 0
  mul_one (a : α)          : a * 1 = a
  left_distrib (a b c : α) : a * (b + c) = a * b + a * c

-- Very simply default `ofNat` for `S`
protected def S.ofNat (α : Type u) [S α] : Nat → α
  | 0   => 0
  | n+1 => S.ofNat α n + 1

instance [S α] : OfNat α n where
  ofNat := S.ofNat α n

instance [S α] : OfNatSound α where
  ofNat_add n m := by
    induction m with
    | zero => simp [S.ofNat]; erw [S.add_zero]; done
    | succ m ih => simp [OfNat.ofNat, S.ofNat] at *; erw [← ih]; rw [S.add_assoc]

theorem S.ofNat_mul [S α] (n m : Nat) : (OfNat.ofNat n : α) * OfNat.ofNat m = OfNat.ofNat (n * m) := by
  induction m with
  | zero => rw [S.mul_zero, Nat.mul_zero]
  | succ m ih =>
    show OfNat.ofNat (α := α) n * OfNat.ofNat (m + 1) = OfNat.ofNat (n * m.succ)
    rw [Nat.mul_succ, ← ofNat_add, ← ofNat_add, ← ih, left_distrib]
    simp [OfNat.ofNat, S.ofNat]
    erw [S.zero_add, S.mul_one]

theorem ex2 [S α] : (100000000000000000 : α) * 20000000000000000 = 2000000000000000000000000000000000  :=
  S.ofNat_mul ..

#print ex2
