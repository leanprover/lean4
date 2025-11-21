open Fin

example (a b : Fin n) : (a % b).val = a.val % b.val := by grind

example (a b : Fin n) : (a * b).val = (a.val * b.val) % n := by grind

example (a : Fin n) : a < n := by grind

example {a b : Fin n} : a.1 ≠ b.1 ↔ a ≠ b := by grind

example (a : Fin n) : a < n := by grind

example {a b : Fin n} : a.1 ≠ b.1 ↔ a ≠ b := by grind

example (a : Fin 1) : a.val = 0 := by grind
example (a : Fin 2) : a.val = 0 ∨ a.val = 1 := by grind

example (a : Fin 37) : a.val < 47 := by grind
example (a : Fin (n + 37)) : a.val < n + 47 := by grind
example (a : Fin (2 * n + 1)) : a.val < 2 * (n + 1) := by grind

example {a b : Fin n} : a ≤ b ↔ a.1 ≤ b.1 := by grind
example {a b : Fin n} : a < b ↔ a.1 < b.1 := by grind
example {a b : Fin n} : a < b ↔ a.val < b.val := by grind
example {a b : Fin n} : ¬ a ≤ b ↔ b < a := by grind
example {a b : Fin n} : ¬ a < b ↔ b ≤ a := by grind
example (a : Fin n) : a ≤ a := by grind
example (a : Fin n) : ¬ a < a := by grind
example {a b c : Fin n} : a ≤ b → b ≤ c → a ≤ c := by grind
example {a b c : Fin n} : a < b → b < c → a < c := by grind
example (a b : Fin n) : a ≤ b ∨ b ≤ a := by grind
example {a b : Fin n} (h : a < b) : ¬ b < a := by grind
example {a b : Fin n} (h : a < b) : a ≠ b := by grind
example {a b : Fin n} (h : a < b) : b ≠ a := by grind
example {a b : Fin n} (h : a < b) : a ≤ b := by grind
example {a b c : Fin n} : a ≤ b → b < c → a < c := by grind
example {a b c : Fin n} : a < b → b ≤ c → a < c := by grind
example {a : Fin n} : a ≤ a := by grind
example {a b : Fin n} : a < b ↔ a ≤ b ∧ a ≠ b := by grind
example {a b : Fin n} (h : a ≠ b) : a < b ∨ b < a := by grind
example (a b : Fin n) : a < b ∨ b ≤ a := by grind
example (a b : Fin n) : a ≤ b ∨ b < a := by grind
example {a b : Fin n} (hab : a = b) : a ≤ b := by grind
example {a b : Fin n} (hab : a = b) : b ≤ a := by grind
example {a b : Fin n} : a ≤ b → a = b ∨ a < b := by grind
example {a b : Fin n} : a ≤ b → a < b ∨ a = b := by grind
example (i : Fin (n + 1)) : i.1 ≤ n := by grind

example {x y : Fin n} : x = y ↔ x ≤ y ∧ y ≤ x := by grind

example [NeZero n] {x : Fin n} : x - x = 0 := by grind

example {n : Nat} : ∀ a b : Fin n, (a * b).val = a.val * b.val % n := by grind

example {n : Nat} : ∀ a b : Fin n, ((a * b : Fin n) : Nat) = a * b % n := by grind

open Std Fin

namespace Fin'

theorem is_lt (a : Fin n) : (a : Nat) < n := by grind

/-! ### coercions and constructions -/

theorem eta (a : Fin n) (h : a < n) : (⟨a, h⟩ : Fin n) = a := by grind

theorem ext {a b : Fin n} (h : (a : Nat) = b) : a = b := by grind

theorem val_ne_iff {a b : Fin n} : a.1 ≠ b.1 ↔ a ≠ b := by grind

theorem forall_iff {p : Fin n → Prop} : (∀ i, p i) ↔ ∀ i h, p ⟨i, h⟩ := by grind [cases Fin]

theorem mk.inj_iff {n a b : Nat} {ha : a < n} {hb : b < n} :
    (⟨a, ha⟩ : Fin n) = ⟨b, hb⟩ ↔ a = b := by grind

theorem val_mk {m n : Nat} (h : m < n) : (⟨m, h⟩ : Fin n).val = m := by grind

theorem mk_val (i : Fin n) : (⟨i, i.isLt⟩ : Fin n) = i := by grind

theorem val_ofNat (n : Nat) [NeZero n] (a : Nat) :
  (Fin.ofNat n a).val = a % n := by grind

theorem mod_val (a b : Fin n) : (a % b).val = a.val % b.val := by grind

theorem div_val (a b : Fin n) : (a / b).val = a.val / b.val := by grind

theorem val_eq_zero (a : Fin 1) : a.val = 0 := by grind

theorem ite_val {n : Nat} {c : Prop} [Decidable c] {x : c → Fin n} (y : ¬c → Fin n) :
    (if h : c then x h else y h).val = if h : c then (x h).val else (y h).val := by grind

theorem dite_val {n : Nat} {c : Prop} [Decidable c] {x y : Fin n} :
    (if c then x else y).val = if c then x.val else y.val := by grind

open IntCast in
theorem intCast_def {n : Nat} [NeZero n] (x : Int) :
    (x : Fin n) = if 0 ≤ x then Fin.ofNat n x.natAbs else -Fin.ofNat n x.natAbs := by grind [Fin.intCast_def]

/-! ### order -/

theorem le_def {a b : Fin n} : a ≤ b ↔ a.1 ≤ b.1 := by grind

theorem lt_def {a b : Fin n} : a < b ↔ a.1 < b.1 := by grind

theorem not_le {a b : Fin n} : ¬ a ≤ b ↔ b < a := by grind

theorem not_lt {a b : Fin n} : ¬ a < b ↔ b ≤ a := by grind

theorem le_refl (a : Fin n) : a ≤ a := by grind

theorem lt_irrefl (a : Fin n) : ¬ a < a := by grind

theorem le_trans {a b c : Fin n} : a ≤ b → b ≤ c → a ≤ c := by grind

theorem lt_trans {a b c : Fin n} : a < b → b < c → a < c := by grind

theorem le_total (a b : Fin n) : a ≤ b ∨ b ≤ a := by grind

theorem lt_asymm {a b : Fin n} (h : a < b) : ¬ b < a := by grind

theorem ne_of_lt {a b : Fin n} (h : a < b) : a ≠ b := by grind

theorem ne_of_gt {a b : Fin n} (h : a < b) : b ≠ a := by grind

theorem le_of_lt {a b : Fin n} (h : a < b) : a ≤ b := by grind

theorem lt_of_le_of_lt {a b c : Fin n} : a ≤ b → b < c → a < c := by grind

theorem lt_of_lt_of_le {a b c : Fin n} : a < b → b ≤ c → a < c := by grind

theorem le_rfl {a : Fin n} : a ≤ a := by grind

theorem lt_iff_le_and_ne {a b : Fin n} : a < b ↔ a ≤ b ∧ a ≠ b := by grind

theorem lt_or_lt_of_ne {a b : Fin n} (h : a ≠ b) : a < b ∨ b < a := by grind

theorem lt_or_le (a b : Fin n) : a < b ∨ b ≤ a := by grind

theorem le_or_lt (a b : Fin n) : a ≤ b ∨ b < a := by grind

theorem le_of_eq {a b : Fin n} (hab : a = b) : a ≤ b := by grind

theorem ge_of_eq {a b : Fin n} (hab : a = b) : b ≤ a := by grind

theorem eq_or_lt_of_le {a b : Fin n} : a ≤ b → a = b ∨ a < b := by grind

theorem lt_or_eq_of_le {a b : Fin n} : a ≤ b → a < b ∨ a = b := by grind

theorem is_le (i : Fin (n + 1)) : i.1 ≤ n := by grind

theorem is_le' {a : Fin n} : a ≤ n := by grind

theorem le_antisymm_iff {x y : Fin n} : x = y ↔ x ≤ y ∧ y ≤ x := by grind

theorem le_antisymm {x y : Fin n} (h1 : x ≤ y) (h2 : y ≤ x) : x = y := by grind

theorem val_rev (i : Fin n) : (rev i).val = n - (i + 1) := by grind

theorem rev_rev (i : Fin n) : rev (rev i) = i := by grind

theorem rev_le_rev {i j : Fin n} : rev i ≤ rev j ↔ j ≤ i := by grind

theorem rev_inj {i j : Fin n} : rev i = rev j ↔ i = j := by grind

theorem rev_lt_rev {i j : Fin n} : rev i < rev j ↔ j < i := by grind

theorem last_zero : (Fin.last 0 : Fin 1) = 0 := by grind

theorem fin_one_eq_zero (a : Fin 1) : a = 0 := by grind

theorem val_add (a b : Fin n) : (a + b).val = (a.val + b.val) % n := by grind

theorem zero_add [NeZero n] (k : Fin n) : (0 : Fin n) + k = k := by grind

theorem add_zero [NeZero n] (k : Fin n) : k + 0 = k := by grind

theorem coe_castLE (h : n ≤ m) (i : Fin n) : (castLE h i : Nat) = i := by grind

theorem cast_cast {k : Nat} (h : n = m) (h' : m = k) {i : Fin n} :
    (i.cast h).cast h' = i.cast (Eq.trans h h') := by grind

theorem castLE_refl (h : n ≤ n) (i : Fin n) : i.castLE h = i := by grind

theorem castSucc_castLE (h : n ≤ m) (i : Fin n) :
    (i.castLE h).castSucc = i.castLE (by omega) := by grind

theorem castSucc_natAdd (n : Nat) (i : Fin k) :
    (i.natAdd n).castSucc = (i.castSucc).natAdd n := by grind

theorem succ_castSucc {n : Nat} (i : Fin n) : i.castSucc.succ = i.succ.castSucc := by grind

theorem natAdd_castSucc {m n : Nat} {i : Fin m} : natAdd n (castSucc i) = castSucc (natAdd n i) := by grind

theorem fin_two_eq_of_eq_zero_iff : ∀ {a b : Fin 2}, (a = 0 ↔ b = 0) → a = b := by grind

theorem sub_self [NeZero n] {x : Fin n} : x - x = 0 := by grind

theorem mul_one [i : NeZero n] (k : Fin n) : k * 1 = k := by grind

theorem mul_comm (a b : Fin n) : a * b = b * a := by grind

theorem mul_assoc (a b c : Fin n) : a * b * c = a * (b * c) := by grind

theorem one_mul [NeZero n] (k : Fin n) : (1 : Fin n) * k = k := by grind

theorem mul_zero [NeZero n] (k : Fin n) : k * 0 = 0 := by grind

theorem zero_mul [NeZero n] (k : Fin n) : (0 : Fin n) * k = 0 := by grind
