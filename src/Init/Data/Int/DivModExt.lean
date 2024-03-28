prelude
import Init.Data.Int.DivModLemmas
import Init.Data.Nat.Lemmas

namespace Int

theorem ediv_ofNat_negSucc (m n : Nat) : m / -[n+1] = -ofNat (m / Nat.succ n) := rfl
theorem ediv_negSucc_zero (m : Nat) : -[m+1] / 0 = 0 := rfl
theorem ediv_negSucc_succ (m n : Nat) : -[m+1] / (n + 1 : Nat) = -((m / (n + 1)) : Nat) + (-1) := by
  simp [HDiv.hDiv, Div.div, Int.ediv, Int.negSucc_coe', Int.sub_eq_add_neg]
theorem ediv_negSucc_negSucc (m n : Nat) : -[m+1] / -[n+1] = ((m / (n + 1) + 1) : Nat) := rfl

theorem emod_ofNat   (a : Nat) (b : Int) : Nat.cast a % b = Nat.cast (a % b.natAbs) := rfl
theorem emod_negSucc (a : Nat) (b : Int) : -[a+1] % b = (b.natAbs : Int) - (a % b.natAbs + 1) := rfl

@[simp] theorem dvd_natCast_natCast (a b : Nat) : (a : Int) ∣ (b : Int) ↔ a ∣ b := by
  simp [Int.dvd_iff_mod_eq_zero, Nat.dvd_iff_mod_eq_zero, mod, Int.emod_ofNat,
    -emod_ofNat]
  apply Int.ofNat_inj

@[simp] theorem dvd_negSucc (a : Int) (b : Nat) : a ∣ -[b +1] ↔ a ∣ (b+1 : Nat) := by
  simp only [Int.dvd_def]
  apply Iff.intro
  · intro ⟨c, p⟩
    apply Exists.intro (-c)
    simp only [Int.mul_neg, ← p]
    rfl
  · intro ⟨c, p⟩
    apply Exists.intro (-c)
    simp only [Int.mul_neg, ← p]
    rfl

@[simp] theorem negSucc_dvd (a : Nat) (b : Int) : -[a +1] ∣ b ↔ (((a+1 : Nat) : Int) ∣ b) := by
  apply Iff.intro
  · intro ⟨c, p⟩
    apply Exists.intro (-c)
    match c with
    | .ofNat 0 =>
      simp_all
    | .ofNat (.succ c) =>
      simp_all [-natCast_add, Int.mul_neg]
    | -[c+1] =>
      simp_all [-natCast_add, Int.mul_neg]
  · intro ⟨c, p⟩
    apply Exists.intro (-c)
    match c with
    | .ofNat 0 =>
      simp_all
    | .ofNat (.succ c) =>
      simp_all [-natCast_add, Int.mul_neg]
    | -[c+1] =>
      simp_all [-natCast_add, Int.mul_neg]

theorem fdiv_eq_ediv' (a b : Int) : Int.fdiv a b = a / b + if b < 0 ∧ ¬(b ∣ a) then (-1) else 0 := by
  match a, b with
  | 0,       b       =>
    simp [Int.fdiv, Int.dvd_zero]
  | ofNat (Nat.succ m), ofNat n =>
    simp [Int.fdiv, Int.ofNat_not_neg]
  | ofNat (Nat.succ m), -[n+1] =>
    simp only [fdiv,Int.negSucc_lt_zero, true_and, Int.ofNat_eq_coe, ediv_ofNat_negSucc,
               Int.negSucc_dvd, Int.dvd_natCast_natCast, ite_not,
               Nat.succ_div, Nat.succ_eq_add_one]
    split <;> rename_i h
    · rw [Int.add_zero]; rfl
    · rw [← Int.neg_add]; rfl
  | -[_+1],  0       =>
    simp
  | -[m+1],  ofNat (Nat.succ n) => rfl
  | -[m+1],  -[n+1]  =>
    simp only [Int.fdiv, Int.ediv_negSucc_negSucc, Nat.succ_div, Int.negSucc_lt_zero, true_and,
      Int.dvd_negSucc, Int.negSucc_dvd, Int.dvd_natCast_natCast]
    split <;> rename_i h
    · simp only [Int.add_zero]
      rfl
    · simp only [Int.natCast_add, Int.Nat.cast_ofNat_Int, Int.add_neg_cancel_right]
      rfl

theorem fmod_eq_emod' (a b : Int) : Int.fmod a b = a % b - b * ite (b < 0 ∧ ¬(b ∣ a)) (-1) 0 := by
  simp [fmod_def, emod_def, fdiv_eq_ediv', Int.sub_eq_add_neg, Int.mul_add, Int.neg_add,
        Int.add_assoc]

end Int
