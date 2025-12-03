/-!
Currently failing examples for `grind`.
Many of these will remain out of scope, and can be deleted as this is decided.
-/

open Fin

namespace Fin'

/-! Challenge problems: -/

theorem mk_eq_zero {n a : Nat} {ha : a < n} [NeZero n] :
    (⟨a, ha⟩ : Fin n) = 0 ↔ a = 0 := by grind

theorem zero_eq_mk {n a : Nat} {ha : a < n} [NeZero n] :
    0 = (⟨a, ha⟩ : Fin n) ↔ a = 0 := by grind

theorem zero_eq_one_iff {n : Nat} [NeZero n] : (0 : Fin n) = 1 ↔ n = 1 := by grind

theorem one_eq_zero_iff {n : Nat} [NeZero n] : (1 : Fin n) = 0 ↔ n = 1 := by grind

theorem val_add_one_of_lt {n : Nat} {i : Fin n.succ} (h : i < last _) : (i + 1).1 = i + 1 := by grind

theorem last_add_one : ∀ n, last n + 1 = 0 := by grind

theorem val_add_one {n : Nat} (i : Fin (n + 1)) :
    ((i + 1 : Fin (n + 1)) : Nat) = if i = last _ then (0 : Nat) else i + 1 := by grind

theorem val_two {n : Nat} : (2 : Fin (n + 3)).val = 2 := by grind

theorem add_one_pos (i : Fin (n + 1)) (h : i < Fin.last n) : (0 : Fin (n + 1)) < i + 1 := by grind

theorem zero_ne_one : (0 : Fin (n + 2)) ≠ 1 := by grind

theorem succ_one_eq_two : Fin.succ (1 : Fin (n + 2)) = 2 := by grind

theorem add_one_lt_iff {n : Nat} {k : Fin (n + 2)} : k + 1 < k ↔ k = last _ := by grind

theorem add_one_le_iff {n : Nat} : ∀ {k : Fin (n + 1)}, k + 1 ≤ k ↔ k = last _ := by grind

theorem lt_add_one_iff {n : Nat} {k : Fin (n + 1)} : k < k + 1 ↔ k < last n := by grind

theorem castSucc_inj {a b : Fin n} : a.castSucc = b.castSucc ↔ a = b := by grind

theorem castSucc_eq_zero_iff [NeZero n] {a : Fin n} : a.castSucc = 0 ↔ a = 0 := by grind

theorem castSucc_ne_zero_iff [NeZero n] {a : Fin n} : a.castSucc ≠ 0 ↔ a ≠ 0 := by grind

theorem coeSucc_eq_succ {a : Fin n} : a.castSucc + 1 = a.succ := by grind

theorem exists_castSucc_eq {n : Nat} {i : Fin (n + 1)} : (∃ j, castSucc j = i) ↔ i ≠ last n := by grind

theorem pred_add_one (i : Fin (n + 2)) (h : (i : Nat) < n + 1) :
    pred (i + 1) (Fin.ne_of_gt (add_one_pos _ (lt_def.2 h))) = castLT i h := by grind

theorem ofNat_add [NeZero n] (x : Nat) (y : Fin n) :
    Fin.ofNat n x + y = Fin.ofNat n (x + y.val) := by grind

theorem add_ofNat [NeZero n] (x : Fin n) (y : Nat) :
    x + Fin.ofNat n y = Fin.ofNat n (x.val + y) := by grind

theorem ofNat_sub [NeZero n] (x : Nat) (y : Fin n) :
    Fin.ofNat n x - y = Fin.ofNat n ((n - y.val) + x) := by grind

private theorem _root_.Nat.mod_eq_sub_of_lt_two_mul {x n} (h₁ : n ≤ x) (h₂ : x < 2 * n) :
    x % n = x - n := by grind

theorem coe_sub_iff_le {a b : Fin n} : (↑(a - b) : Nat) = a - b ↔ b ≤ a := by grind

theorem sub_val_of_le {a b : Fin n} : b ≤ a → (a - b).val = a.val - b.val := by grind

theorem coe_sub_iff_lt {a b : Fin n} : (↑(a - b) : Nat) = n + a - b ↔ a < b := by grind

theorem sub_eq_add_neg {n : Nat} (x y : Fin n) : x - y = x + -y := by grind [Fin.val_add]

theorem ofNat_mul [NeZero n] (x : Nat) (y : Fin n) :
    Fin.ofNat n x * y = Fin.ofNat n (x * y.val) := by grind

theorem mul_ofNat [NeZero n] (x : Fin n) (y : Nat) :
    x * Fin.ofNat n y = Fin.ofNat n (x.val * y) := by grind

/-! Shouldn't expect to work by `grind`: -/

theorem pos_iff_nonempty {n : Nat} : 0 < n ↔ Nonempty (Fin n) := by grind

theorem eq_zero_or_eq_succ {n : Nat} : ∀ i : Fin (n + 1), i = 0 ∨ ∃ j : Fin n, i = j.succ := by grind

theorem eq_succ_of_ne_zero {n : Nat} {i : Fin (n + 1)} (hi : i ≠ 0) : ∃ j : Fin n, i = j.succ := by grind

theorem subsingleton_iff_le_one : Subsingleton (Fin n) ↔ n ≤ 1 := by grind

instance subsingleton_zero : Subsingleton (Fin 0) := by grind

instance subsingleton_one : Subsingleton (Fin 1) := by grind

theorem forall_fin_succ {P : Fin (n + 1) → Prop} : (∀ i, P i) ↔ P 0 ∧ ∀ i : Fin n, P i.succ := by grind

theorem exists_fin_succ {P : Fin (n + 1) → Prop} : (∃ i, P i) ↔ P 0 ∨ ∃ i : Fin n, P i.succ := by grind

theorem forall_fin_zero {p : Fin 0 → Prop} : (∀ i, p i) ↔ True := by grind

theorem exists_fin_zero {p : Fin 0 → Prop} : (∃ i, p i) ↔ False := by grind

theorem forall_fin_one {p : Fin 1 → Prop} : (∀ i, p i) ↔ p 0 := by grind

theorem exists_fin_one {p : Fin 1 → Prop} : (∃ i, p i) ↔ p 0 := by grind

theorem forall_fin_two {p : Fin 2 → Prop} : (∀ i, p i) ↔ p 0 ∧ p 1 := by grind

theorem exists_fin_two {p : Fin 2 → Prop} : (∃ i, p i) ↔ p 0 ∨ p 1 := by grind

end Fin'
