/-
Copyright (c) 2022 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Leonardo de Moura
-/
prelude
import Init.Data.Fin.Basic
import Init.Data.Nat.Lemmas
import Init.Ext
import Init.ByCases
import Init.Conv
import Init.Omega

namespace Fin

@[simp] theorem ofNat'_zero (n : Nat) [NeZero n] : Fin.ofNat' n 0 = 0 := rfl

@[deprecated Fin.pos (since := "2024-11-11")]
theorem size_pos (i : Fin n) : 0 < n := i.pos

theorem mod_def (a m : Fin n) : a % m = Fin.mk (a % m) (Nat.lt_of_le_of_lt (Nat.mod_le _ _) a.2) :=
  rfl

theorem mul_def (a b : Fin n) : a * b = Fin.mk ((a * b) % n) (Nat.mod_lt _ a.pos) := rfl

theorem sub_def (a b : Fin n) : a - b = Fin.mk (((n - b) + a) % n) (Nat.mod_lt _ a.pos) := rfl

theorem pos' : ∀ [Nonempty (Fin n)], 0 < n | ⟨i⟩ => i.pos

@[deprecated pos' (since := "2024-11-11")] abbrev size_pos' := @pos'

@[simp] theorem is_lt (a : Fin n) : (a : Nat) < n := a.2

theorem pos_iff_nonempty {n : Nat} : 0 < n ↔ Nonempty (Fin n) :=
  ⟨fun h => ⟨⟨0, h⟩⟩, fun ⟨i⟩ => i.pos⟩

/-! ### coercions and constructions -/

@[simp] protected theorem eta (a : Fin n) (h : a < n) : (⟨a, h⟩ : Fin n) = a := rfl

@[ext] protected theorem ext {a b : Fin n} (h : (a : Nat) = b) : a = b := eq_of_val_eq h

theorem val_ne_iff {a b : Fin n} : a.1 ≠ b.1 ↔ a ≠ b := not_congr val_inj

theorem forall_iff {p : Fin n → Prop} : (∀ i, p i) ↔ ∀ i h, p ⟨i, h⟩ :=
  ⟨fun h i hi => h ⟨i, hi⟩, fun h ⟨i, hi⟩ => h i hi⟩

/-- Restatement of `Fin.mk.injEq` as an `iff`. -/
protected theorem mk.inj_iff {n a b : Nat} {ha : a < n} {hb : b < n} :
    (⟨a, ha⟩ : Fin n) = ⟨b, hb⟩ ↔ a = b := Fin.ext_iff

theorem val_mk {m n : Nat} (h : m < n) : (⟨m, h⟩ : Fin n).val = m := rfl

theorem eq_mk_iff_val_eq {a : Fin n} {k : Nat} {hk : k < n} :
    a = ⟨k, hk⟩ ↔ (a : Nat) = k := Fin.ext_iff

theorem mk_val (i : Fin n) : (⟨i, i.isLt⟩ : Fin n) = i := Fin.eta ..

@[simp] theorem mk_eq_zero {n a : Nat} {ha : a < n} [NeZero n] :
    (⟨a, ha⟩ : Fin n) = 0 ↔ a = 0 :=
  mk.inj_iff

@[simp] theorem zero_eq_mk {n a : Nat} {ha : a < n} [NeZero n] :
    0 = (⟨a, ha⟩ : Fin n) ↔ a = 0 := by
  simp [eq_comm]

@[simp] theorem val_ofNat' (n : Nat) [NeZero n] (a : Nat) :
  (Fin.ofNat' n a).val = a % n := rfl

@[simp] theorem ofNat'_self {n : Nat} [NeZero n] : Fin.ofNat' n n = 0 := by
  ext
  simp
  congr

@[simp] theorem ofNat'_val_eq_self [NeZero n] (x : Fin n) : (Fin.ofNat' n x) = x := by
  ext
  rw [val_ofNat', Nat.mod_eq_of_lt]
  exact x.2

@[simp] theorem mod_val (a b : Fin n) : (a % b).val = a.val % b.val :=
  rfl

@[simp] theorem div_val (a b : Fin n) : (a / b).val = a.val / b.val :=
  rfl

@[simp] theorem modn_val (a : Fin n) (b : Nat) : (a.modn b).val = a.val % b :=
  rfl

@[simp] theorem val_eq_zero (a : Fin 1) : a.val = 0 :=
  Nat.eq_zero_of_le_zero <| Nat.le_of_lt_succ a.isLt

theorem ite_val {n : Nat} {c : Prop} [Decidable c] {x : c → Fin n} (y : ¬c → Fin n) :
    (if h : c then x h else y h).val = if h : c then (x h).val else (y h).val := by
  by_cases c <;> simp [*]

theorem dite_val {n : Nat} {c : Prop} [Decidable c] {x y : Fin n} :
    (if c then x else y).val = if c then x.val else y.val := by
  by_cases c <;> simp [*]

/-! ### order -/

theorem le_def {a b : Fin n} : a ≤ b ↔ a.1 ≤ b.1 := .rfl

theorem lt_def {a b : Fin n} : a < b ↔ a.1 < b.1 := .rfl

theorem lt_iff_val_lt_val {a b : Fin n} : a < b ↔ a.val < b.val := Iff.rfl

@[simp] protected theorem not_le {a b : Fin n} : ¬ a ≤ b ↔ b < a := Nat.not_le

@[simp] protected theorem not_lt {a b : Fin n} : ¬ a < b ↔ b ≤ a := Nat.not_lt

@[simp] protected theorem le_refl (a : Fin n) : a ≤ a := by simp [le_def]

@[simp] protected theorem lt_irrefl (a : Fin n) : ¬ a < a := by simp

protected theorem le_trans {a b c : Fin n} : a ≤ b → b ≤ c → a ≤ c := Nat.le_trans

protected theorem lt_trans {a b c : Fin n} : a < b → b < c → a < c := Nat.lt_trans

protected theorem le_total (a b : Fin n) : a ≤ b ∨ b ≤ a := Nat.le_total a b

protected theorem lt_asymm {a b : Fin n} (h : a < b) : ¬ b < a := Nat.lt_asymm h

protected theorem ne_of_lt {a b : Fin n} (h : a < b) : a ≠ b := Fin.ne_of_val_ne (Nat.ne_of_lt h)

protected theorem ne_of_gt {a b : Fin n} (h : a < b) : b ≠ a := Fin.ne_of_val_ne (Nat.ne_of_gt h)

protected theorem le_of_lt {a b : Fin n} (h : a < b) : a ≤ b := Nat.le_of_lt h

theorem is_le (i : Fin (n + 1)) : i ≤ n := Nat.le_of_lt_succ i.is_lt

@[simp] theorem is_le' {a : Fin n} : a ≤ n := Nat.le_of_lt a.is_lt

theorem mk_lt_of_lt_val {b : Fin n} {a : Nat} (h : a < b) :
    (⟨a, Nat.lt_trans h b.is_lt⟩ : Fin n) < b := h

theorem mk_le_of_le_val {b : Fin n} {a : Nat} (h : a ≤ b) :
    (⟨a, Nat.lt_of_le_of_lt h b.is_lt⟩ : Fin n) ≤ b := h

@[simp] theorem mk_le_mk {x y : Nat} {hx hy} : (⟨x, hx⟩ : Fin n) ≤ ⟨y, hy⟩ ↔ x ≤ y := .rfl

@[simp] theorem mk_lt_mk {x y : Nat} {hx hy} : (⟨x, hx⟩ : Fin n) < ⟨y, hy⟩ ↔ x < y := .rfl

@[simp] theorem val_zero (n : Nat) [NeZero n] : ((0 : Fin n) : Nat) = 0 := rfl

@[simp] theorem mk_zero : (⟨0, Nat.succ_pos n⟩ : Fin (n + 1)) = 0 := rfl

@[simp] theorem zero_le (a : Fin (n + 1)) : 0 ≤ a := Nat.zero_le a.val

theorem zero_lt_one : (0 : Fin (n + 2)) < 1 := Nat.zero_lt_one

@[simp] theorem not_lt_zero (a : Fin (n + 1)) : ¬a < 0 := nofun

theorem pos_iff_ne_zero {a : Fin (n + 1)} : 0 < a ↔ a ≠ 0 := by
  rw [lt_def, val_zero, Nat.pos_iff_ne_zero, ← val_ne_iff]; rfl

theorem eq_zero_or_eq_succ {n : Nat} : ∀ i : Fin (n + 1), i = 0 ∨ ∃ j : Fin n, i = j.succ
  | 0 => .inl rfl
  | ⟨j + 1, h⟩ => .inr ⟨⟨j, Nat.lt_of_succ_lt_succ h⟩, rfl⟩

theorem eq_succ_of_ne_zero {n : Nat} {i : Fin (n + 1)} (hi : i ≠ 0) : ∃ j : Fin n, i = j.succ :=
  (eq_zero_or_eq_succ i).resolve_left hi

protected theorem le_antisymm_iff {x y : Fin n} : x = y ↔ x ≤ y ∧ y ≤ x :=
  Fin.ext_iff.trans Nat.le_antisymm_iff

protected theorem le_antisymm {x y : Fin n} (h1 : x ≤ y) (h2 : y ≤ x) : x = y :=
  Fin.le_antisymm_iff.2 ⟨h1, h2⟩

@[simp] theorem val_rev (i : Fin n) : rev i = n - (i + 1) := rfl

@[simp] theorem rev_rev (i : Fin n) : rev (rev i) = i := Fin.ext <| by
  rw [val_rev, val_rev, ← Nat.sub_sub, Nat.sub_sub_self (by exact i.2), Nat.add_sub_cancel]

@[simp] theorem rev_le_rev {i j : Fin n} : rev i ≤ rev j ↔ j ≤ i := by
  simp only [le_def, val_rev, Nat.sub_le_sub_iff_left (Nat.succ_le.2 j.is_lt)]
  exact Nat.succ_le_succ_iff

@[simp] theorem rev_inj {i j : Fin n} : rev i = rev j ↔ i = j :=
  ⟨fun h => by simpa using congrArg rev h, congrArg _⟩

theorem rev_eq {n a : Nat} (i : Fin (n + 1)) (h : n = a + i) :
    rev i = ⟨a, Nat.lt_succ_of_le (h ▸ Nat.le_add_right ..)⟩ := by
  ext; dsimp
  conv => lhs; congr; rw [h]
  rw [Nat.add_assoc, Nat.add_sub_cancel]

@[simp] theorem rev_lt_rev {i j : Fin n} : rev i < rev j ↔ j < i := by
  rw [← Fin.not_le, ← Fin.not_le, rev_le_rev]

/-! ### last -/

@[simp] theorem val_last (n : Nat) : last n = n := rfl

@[simp] theorem last_zero : (Fin.last 0 : Fin 1) = 0 := by
  ext
  simp

@[simp] theorem zero_eq_last_iff {n : Nat} : (0 : Fin (n + 1)) = last n ↔ n = 0 := by
  constructor
  · intro h
    simp_all [Fin.ext_iff]
  · rintro rfl
    simp

@[simp] theorem last_eq_zero_iff {n : Nat} : Fin.last n = 0 ↔ n = 0 := by
  simp [eq_comm (a := Fin.last n)]

theorem le_last (i : Fin (n + 1)) : i ≤ last n := Nat.le_of_lt_succ i.is_lt

theorem last_pos : (0 : Fin (n + 2)) < last (n + 1) := Nat.succ_pos _

theorem eq_last_of_not_lt {i : Fin (n + 1)} (h : ¬(i : Nat) < n) : i = last n :=
  Fin.ext <| Nat.le_antisymm (le_last i) (Nat.not_lt.1 h)

theorem val_lt_last {i : Fin (n + 1)} : i ≠ last n → (i : Nat) < n :=
  Decidable.not_imp_comm.1 eq_last_of_not_lt

@[simp] theorem rev_last (n : Nat) : rev (last n) = 0 := Fin.ext <| by simp

@[simp] theorem rev_zero (n : Nat) : rev 0 = last n := by
  rw [← rev_rev (last _), rev_last]

/-! ### addition, numerals, and coercion from Nat -/

@[simp] theorem val_one (n : Nat) : (1 : Fin (n + 2)).val = 1 := rfl

@[simp] theorem mk_one : (⟨1, Nat.succ_lt_succ (Nat.succ_pos n)⟩ : Fin (n + 2)) = (1 : Fin _) := rfl

theorem subsingleton_iff_le_one : Subsingleton (Fin n) ↔ n ≤ 1 := by
  (match n with | 0 | 1 | n+2 => ?_) <;> try simp
  · exact ⟨nofun⟩
  · exact ⟨fun ⟨0, _⟩ ⟨0, _⟩ => rfl⟩
  · exact iff_of_false (fun h => Fin.ne_of_lt zero_lt_one (h.elim ..)) (of_decide_eq_false rfl)

instance subsingleton_zero : Subsingleton (Fin 0) := subsingleton_iff_le_one.2 (by decide)

instance subsingleton_one : Subsingleton (Fin 1) := subsingleton_iff_le_one.2 (by decide)

theorem fin_one_eq_zero (a : Fin 1) : a = 0 := Subsingleton.elim a 0

@[simp] theorem zero_eq_one_iff {n : Nat} [NeZero n] : (0 : Fin n) = 1 ↔ n = 1 := by
  constructor
  · intro h
    simp [Fin.ext_iff] at h
    change 0 % n = 1 % n at h
    rw [eq_comm] at h
    simpa using h
  · rintro rfl
    simp

@[simp] theorem one_eq_zero_iff {n : Nat} [NeZero n] : (1 : Fin n) = 0 ↔ n = 1 := by
  rw [eq_comm]
  simp

theorem add_def (a b : Fin n) : a + b = Fin.mk ((a + b) % n) (Nat.mod_lt _ a.pos) := rfl

theorem val_add (a b : Fin n) : (a + b).val = (a.val + b.val) % n := rfl

@[simp] protected theorem zero_add [NeZero n] (k : Fin n) : (0 : Fin n) + k = k := by
  ext
  simp [Fin.add_def, Nat.mod_eq_of_lt k.2]

@[simp] protected theorem add_zero [NeZero n] (k : Fin n) : k + 0 = k := by
  ext
  simp [add_def, Nat.mod_eq_of_lt k.2]

theorem val_add_one_of_lt {n : Nat} {i : Fin n.succ} (h : i < last _) : (i + 1).1 = i + 1 := by
  match n with
  | 0 => cases h
  | n+1 => rw [val_add, val_one, Nat.mod_eq_of_lt (by exact Nat.succ_lt_succ h)]

@[simp] theorem last_add_one : ∀ n, last n + 1 = 0
  | 0 => rfl
  | n + 1 => by ext; rw [val_add, val_zero, val_last, val_one, Nat.mod_self]

theorem val_add_one {n : Nat} (i : Fin (n + 1)) :
    ((i + 1 : Fin (n + 1)) : Nat) = if i = last _ then (0 : Nat) else i + 1 := by
  match Nat.eq_or_lt_of_le (le_last i) with
  | .inl h => cases Fin.eq_of_val_eq h; simp
  | .inr h => simpa [Fin.ne_of_lt h] using val_add_one_of_lt h

@[simp] theorem val_two {n : Nat} : (2 : Fin (n + 3)).val = 2 := rfl

theorem add_one_pos (i : Fin (n + 1)) (h : i < Fin.last n) : (0 : Fin (n + 1)) < i + 1 := by
  match n with
  | 0 => cases h
  | n+1 =>
    rw [Fin.lt_def, val_last, ← Nat.add_lt_add_iff_right] at h
    rw [Fin.lt_def, val_add, val_zero, val_one, Nat.mod_eq_of_lt h]
    exact Nat.zero_lt_succ _

theorem one_pos : (0 : Fin (n + 2)) < 1 := Nat.succ_pos 0

theorem zero_ne_one : (0 : Fin (n + 2)) ≠ 1 := Fin.ne_of_lt one_pos

/-! ### succ and casts into larger Fin types -/

@[simp] theorem val_succ (j : Fin n) : (j.succ : Nat) = j + 1 := rfl

@[simp] theorem succ_pos (a : Fin n) : (0 : Fin (n + 1)) < a.succ := by
  simp [Fin.lt_def, Nat.succ_pos]

@[simp] theorem succ_le_succ_iff {a b : Fin n} : a.succ ≤ b.succ ↔ a ≤ b := Nat.succ_le_succ_iff

@[simp] theorem succ_lt_succ_iff {a b : Fin n} : a.succ < b.succ ↔ a < b := Nat.succ_lt_succ_iff

@[simp] theorem succ_inj {a b : Fin n} : a.succ = b.succ ↔ a = b := by
  refine ⟨fun h => Fin.ext ?_, congrArg _⟩
  apply Nat.le_antisymm <;> exact succ_le_succ_iff.1 (h ▸ Nat.le_refl _)

theorem succ_ne_zero {n} : ∀ k : Fin n, Fin.succ k ≠ 0
  | ⟨k, _⟩, heq => Nat.succ_ne_zero k <| congrArg Fin.val heq

@[simp] theorem succ_zero_eq_one : Fin.succ (0 : Fin (n + 1)) = 1 := rfl

/-- Version of `succ_one_eq_two` to be used by `dsimp` -/
@[simp] theorem succ_one_eq_two : Fin.succ (1 : Fin (n + 2)) = 2 := rfl

@[simp] theorem succ_mk (n i : Nat) (h : i < n) :
    Fin.succ ⟨i, h⟩ = ⟨i + 1, Nat.succ_lt_succ h⟩ := rfl

theorem mk_succ_pos (i : Nat) (h : i < n) :
    (0 : Fin (n + 1)) < ⟨i.succ, Nat.add_lt_add_right h 1⟩ := by
  rw [lt_def, val_zero]; exact Nat.succ_pos i

theorem one_lt_succ_succ (a : Fin n) : (1 : Fin (n + 2)) < a.succ.succ := by
  let n+1 := n
  rw [← succ_zero_eq_one, succ_lt_succ_iff]; exact succ_pos a

@[simp] theorem add_one_lt_iff {n : Nat} {k : Fin (n + 2)} : k + 1 < k ↔ k = last _ := by
  simp only [lt_def, val_add, val_last, Fin.ext_iff]
  let ⟨k, hk⟩ := k
  match Nat.eq_or_lt_of_le (Nat.le_of_lt_succ hk) with
  | .inl h => cases h; simp [Nat.succ_pos]
  | .inr hk' => simp [Nat.ne_of_lt hk', Nat.mod_eq_of_lt (Nat.succ_lt_succ hk'), Nat.le_succ]

@[simp] theorem add_one_le_iff {n : Nat} : ∀ {k : Fin (n + 1)}, k + 1 ≤ k ↔ k = last _ := by
  match n with
  | 0 =>
    intro (k : Fin 1)
    exact iff_of_true (Subsingleton.elim (α := Fin 1) (k+1) _ ▸ Nat.le_refl _) (fin_one_eq_zero ..)
  | n + 1 =>
    intro (k : Fin (n+2))
    rw [← add_one_lt_iff, lt_def, le_def, Nat.lt_iff_le_and_ne, and_iff_left]
    rw [val_add_one]
    split <;> simp [*, (Nat.succ_ne_zero _).symm, Nat.ne_of_gt (Nat.lt_succ_self _)]

@[simp] theorem last_le_iff {n : Nat} {k : Fin (n + 1)} : last n ≤ k ↔ k = last n := by
  rw [Fin.ext_iff, Nat.le_antisymm_iff, le_def, and_iff_right (by apply le_last)]

@[simp] theorem lt_add_one_iff {n : Nat} {k : Fin (n + 1)} : k < k + 1 ↔ k < last n := by
  rw [← Decidable.not_iff_not]; simp

@[simp] theorem le_zero_iff {n : Nat} {k : Fin (n + 1)} : k ≤ 0 ↔ k = 0 :=
  ⟨fun h => Fin.eq_of_val_eq <| Nat.eq_zero_of_le_zero h, (· ▸ Nat.le_refl _)⟩

theorem succ_succ_ne_one (a : Fin n) : Fin.succ (Fin.succ a) ≠ 1 :=
  Fin.ne_of_gt (one_lt_succ_succ a)

@[simp] theorem coe_castLT (i : Fin m) (h : i.1 < n) : (castLT i h : Nat) = i := rfl

@[simp] theorem castLT_mk (i n m : Nat) (hn : i < n) (hm : i < m) : castLT ⟨i, hn⟩ hm = ⟨i, hm⟩ :=
  rfl

@[simp] theorem coe_castLE (h : n ≤ m) (i : Fin n) : (castLE h i : Nat) = i := rfl

@[simp] theorem castLE_mk (i n m : Nat) (hn : i < n) (h : n ≤ m) :
    castLE h ⟨i, hn⟩ = ⟨i, Nat.lt_of_lt_of_le hn h⟩ := rfl

@[simp] theorem castLE_zero {n m : Nat} (h : n.succ ≤ m.succ) : castLE h 0 = 0 := by simp [Fin.ext_iff]

@[simp] theorem castLE_succ {m n : Nat} (h : m + 1 ≤ n + 1) (i : Fin m) :
    castLE h i.succ = (castLE (Nat.succ_le_succ_iff.mp h) i).succ := by simp [Fin.ext_iff]

@[simp] theorem castLE_castLE {k m n} (km : k ≤ m) (mn : m ≤ n) (i : Fin k) :
    Fin.castLE mn (Fin.castLE km i) = Fin.castLE (Nat.le_trans km mn) i :=
  Fin.ext (by simp only [coe_castLE])

@[simp] theorem castLE_comp_castLE {k m n} (km : k ≤ m) (mn : m ≤ n) :
    Fin.castLE mn ∘ Fin.castLE km = Fin.castLE (Nat.le_trans km mn) :=
  funext (castLE_castLE km mn)

@[simp] theorem coe_cast (h : n = m) (i : Fin n) : (i.cast h : Nat) = i := rfl

@[simp] theorem cast_zero [NeZero n] [NeZero m] (h : n = m) : Fin.cast h 0 = 0 := rfl

@[simp] theorem cast_last {n' : Nat} {h : n + 1 = n' + 1} : (last n).cast h  = last n' :=
  Fin.ext (by rw [coe_cast, val_last, val_last, Nat.succ.inj h])

@[simp] theorem cast_mk (h : n = m) (i : Nat) (hn : i < n) : Fin.cast h ⟨i, hn⟩ = ⟨i, h ▸ hn⟩ := rfl

@[simp] theorem cast_refl (n : Nat) (h : n = n) : Fin.cast h = id := by
  ext
  simp

@[simp] theorem cast_trans {k : Nat} (h : n = m) (h' : m = k) {i : Fin n} :
    (i.cast h).cast h' = i.cast (Eq.trans h h') := rfl

theorem castLE_of_eq {m n : Nat} (h : m = n) {h' : m ≤ n} : castLE h' = Fin.cast h := rfl

@[simp] theorem coe_castAdd (m : Nat) (i : Fin n) : (castAdd m i : Nat) = i := rfl

@[simp] theorem castAdd_zero : (castAdd 0 : Fin n → Fin (n + 0)) = Fin.cast rfl := rfl

theorem castAdd_lt {m : Nat} (n : Nat) (i : Fin m) : (castAdd n i : Nat) < m := by simp

@[simp] theorem castAdd_mk (m : Nat) (i : Nat) (h : i < n) :
    castAdd m ⟨i, h⟩ = ⟨i, Nat.lt_add_right m h⟩ := rfl

@[simp] theorem castAdd_castLT (m : Nat) (i : Fin (n + m)) (hi : i.val < n) :
    castAdd m (castLT i hi) = i := rfl

@[simp] theorem castLT_castAdd (m : Nat) (i : Fin n) :
    castLT (castAdd m i) (castAdd_lt m i) = i := rfl

/-- For rewriting in the reverse direction, see `Fin.cast_castAdd_left`. -/
theorem castAdd_cast {n n' : Nat} (m : Nat) (i : Fin n') (h : n' = n) :
    castAdd m (Fin.cast h i) = Fin.cast (congrArg (. + m) h) (castAdd m i) := Fin.ext rfl

theorem cast_castAdd_left {n n' m : Nat} (i : Fin n') (h : n' + m = n + m) :
    (i.castAdd m).cast h = (i.cast (Nat.add_right_cancel h)).castAdd m := rfl

@[simp] theorem cast_castAdd_right {n m m' : Nat} (i : Fin n) (h : n + m' = n + m) :
    (i.castAdd m').cast h = i.castAdd m := rfl

theorem castAdd_castAdd {m n p : Nat} (i : Fin m) :
    (i.castAdd n).castAdd p = (i.castAdd (n + p)).cast (Nat.add_assoc ..).symm  := rfl

/-- The cast of the successor is the successor of the cast. See `Fin.succ_cast_eq` for rewriting in
the reverse direction. -/
@[simp] theorem cast_succ_eq {n' : Nat} (i : Fin n) (h : n.succ = n'.succ) :
    i.succ.cast h = (i.cast (Nat.succ.inj h)).succ := rfl

theorem succ_cast_eq {n' : Nat} (i : Fin n) (h : n = n') :
    (i.cast h).succ = i.succ.cast (by rw [h]) := rfl

@[simp] theorem coe_castSucc (i : Fin n) : (i.castSucc : Nat) = i := rfl

@[simp] theorem castSucc_mk (n i : Nat) (h : i < n) : castSucc ⟨i, h⟩ = ⟨i, Nat.lt.step h⟩ := rfl

@[simp] theorem cast_castSucc {n' : Nat} {h : n + 1 = n' + 1} {i : Fin n} :
    i.castSucc.cast h = (i.cast (Nat.succ.inj h)).castSucc := rfl

theorem castSucc_lt_succ (i : Fin n) : i.castSucc < i.succ :=
  lt_def.2 <| by simp only [coe_castSucc, val_succ, Nat.lt_succ_self]

theorem le_castSucc_iff {i : Fin (n + 1)} {j : Fin n} : i ≤ j.castSucc ↔ i < j.succ := by
  simpa only [lt_def, le_def] using Nat.add_one_le_add_one_iff.symm

theorem castSucc_lt_iff_succ_le {n : Nat} {i : Fin n} {j : Fin (n + 1)} :
    i.castSucc < j ↔ i.succ ≤ j := .rfl

@[simp] theorem succ_last (n : Nat) : (last n).succ = last n.succ := rfl

@[simp] theorem succ_eq_last_succ {n : Nat} {i : Fin n.succ} :
    i.succ = last (n + 1) ↔ i = last n := by rw [← succ_last, succ_inj]

@[simp] theorem castSucc_castLT (i : Fin (n + 1)) (h : (i : Nat) < n) :
    (castLT i h).castSucc = i := rfl

@[simp] theorem castLT_castSucc {n : Nat} (a : Fin n) (h : (a : Nat) < n) :
    castLT a.castSucc h = a := rfl

@[simp] theorem castSucc_lt_castSucc_iff {a b : Fin n} :
    a.castSucc < b.castSucc ↔ a < b := .rfl

theorem castSucc_inj {a b : Fin n} : a.castSucc = b.castSucc ↔ a = b := by simp [Fin.ext_iff]

theorem castSucc_lt_last (a : Fin n) : a.castSucc < last n := a.is_lt

@[simp] theorem castSucc_zero : castSucc (0 : Fin (n + 1)) = 0 := rfl

@[simp] theorem castSucc_one {n : Nat} : castSucc (1 : Fin (n + 2)) = 1 := rfl

/-- `castSucc i` is positive when `i` is positive -/
theorem castSucc_pos {i : Fin (n + 1)} (h : 0 < i) : 0 < i.castSucc := by
  simpa [lt_def] using h

@[simp] theorem castSucc_eq_zero_iff {a : Fin (n + 1)} : a.castSucc = 0 ↔ a = 0 := by simp [Fin.ext_iff]

theorem castSucc_ne_zero_iff {a : Fin (n + 1)} : a.castSucc ≠ 0 ↔ a ≠ 0 :=
  not_congr <| castSucc_eq_zero_iff

theorem castSucc_fin_succ (n : Nat) (j : Fin n) :
    j.succ.castSucc = (j.castSucc).succ := by simp [Fin.ext_iff]

@[simp]
theorem coeSucc_eq_succ {a : Fin n} : a.castSucc + 1 = a.succ := by
  cases n
  · exact a.elim0
  · simp [Fin.ext_iff, add_def, Nat.mod_eq_of_lt (Nat.succ_lt_succ a.is_lt)]

theorem lt_succ {a : Fin n} : a.castSucc < a.succ := by
  rw [castSucc, lt_def, coe_castAdd, val_succ]; exact Nat.lt_succ_self a.val

theorem exists_castSucc_eq {n : Nat} {i : Fin (n + 1)} : (∃ j, castSucc j = i) ↔ i ≠ last n :=
  ⟨fun ⟨j, hj⟩ => hj ▸ Fin.ne_of_lt j.castSucc_lt_last,
   fun hi => ⟨i.castLT <| Fin.val_lt_last hi, rfl⟩⟩

theorem succ_castSucc {n : Nat} (i : Fin n) : i.castSucc.succ = i.succ.castSucc := rfl

@[simp] theorem coe_addNat (m : Nat) (i : Fin n) : (addNat i m : Nat) = i + m := rfl

@[simp] theorem addNat_zero (n : Nat) (i : Fin n) : addNat i 0 = i := by
  ext
  simp

@[simp] theorem addNat_one {i : Fin n} : addNat i 1 = i.succ := rfl

theorem le_coe_addNat (m : Nat) (i : Fin n) : m ≤ addNat i m :=
  Nat.le_add_left _ _

@[simp] theorem addNat_mk (n i : Nat) (hi : i < m) :
    addNat ⟨i, hi⟩ n = ⟨i + n, Nat.add_lt_add_right hi n⟩ := rfl

@[simp] theorem cast_addNat_zero {n n' : Nat} (i : Fin n) (h : n + 0 = n') :
    (addNat i 0).cast h = i.cast ((Nat.add_zero _).symm.trans h) := rfl

/-- For rewriting in the reverse direction, see `Fin.cast_addNat_left`. -/
theorem addNat_cast {n n' m : Nat} (i : Fin n') (h : n' = n) :
    addNat (i.cast h) m = (addNat i m).cast (congrArg (. + m) h) := rfl

theorem cast_addNat_left {n n' m : Nat} (i : Fin n') (h : n' + m = n + m) :
    (addNat i m).cast h = addNat (i.cast (Nat.add_right_cancel h)) m := rfl

@[simp] theorem cast_addNat_right {n m m' : Nat} (i : Fin n) (h : n + m' = n + m) :
    (addNat i m').cast h = addNat i m :=
  Fin.ext <| (congrArg ((· + ·) (i : Nat)) (Nat.add_left_cancel h) : _)

@[simp] theorem coe_natAdd (n : Nat) {m : Nat} (i : Fin m) : (natAdd n i : Nat) = n + i := rfl

@[simp] theorem natAdd_mk (n i : Nat) (hi : i < m) :
    natAdd n ⟨i, hi⟩ = ⟨n + i, Nat.add_lt_add_left hi n⟩ := rfl

theorem le_coe_natAdd (m : Nat) (i : Fin n) : m ≤ natAdd m i := Nat.le_add_right ..

@[simp] theorem natAdd_zero {n : Nat} : natAdd 0 = Fin.cast (Nat.zero_add n).symm := by ext; simp

/-- For rewriting in the reverse direction, see `Fin.cast_natAdd_right`. -/
theorem natAdd_cast {n n' : Nat} (m : Nat) (i : Fin n') (h : n' = n) :
    natAdd m (i.cast h) = (natAdd m i).cast (congrArg _ h) := rfl

theorem cast_natAdd_right {n n' m : Nat} (i : Fin n') (h : m + n' = m + n) :
    (natAdd m i).cast h  = natAdd m (i.cast (Nat.add_left_cancel h)) := rfl

@[simp] theorem cast_natAdd_left {n m m' : Nat} (i : Fin n) (h : m' + n = m + n) :
    (natAdd m' i).cast h = natAdd m i :=
  Fin.ext <| (congrArg (· + (i : Nat)) (Nat.add_right_cancel h) : _)

theorem castAdd_natAdd (p m : Nat) {n : Nat} (i : Fin n) :
    castAdd p (natAdd m i) = (natAdd m (castAdd p i)).cast (Nat.add_assoc ..).symm := rfl

theorem natAdd_castAdd (p m : Nat) {n : Nat} (i : Fin n) :
    natAdd m (castAdd p i) = (castAdd p (natAdd m i)).cast (Nat.add_assoc ..) := rfl

theorem natAdd_natAdd (m n : Nat) {p : Nat} (i : Fin p) :
    natAdd m (natAdd n i) = (natAdd (m + n) i).cast (Nat.add_assoc ..) :=
  Fin.ext <| (Nat.add_assoc ..).symm

theorem cast_natAdd_zero {n n' : Nat} (i : Fin n) (h : 0 + n = n') :
    (natAdd 0 i).cast h = i.cast ((Nat.zero_add _).symm.trans h) := by simp

@[simp]
theorem cast_natAdd (n : Nat) {m : Nat} (i : Fin m) :
    (natAdd n i).cast (Nat.add_comm ..) = addNat i n := Fin.ext <| Nat.add_comm ..

@[simp]
theorem cast_addNat {n : Nat} (m : Nat) (i : Fin n) :
    (addNat i m).cast (Nat.add_comm ..) = natAdd m i := Fin.ext <| Nat.add_comm ..

@[simp] theorem natAdd_last {m n : Nat} : natAdd n (last m) = last (n + m) := rfl

@[simp] theorem addNat_last (n : Nat) :
    addNat (last n) m = (last (n + m)).cast (by omega) := by
  ext
  simp

theorem natAdd_castSucc {m n : Nat} {i : Fin m} : natAdd n (castSucc i) = castSucc (natAdd n i) :=
  rfl

@[simp] theorem natAdd_eq_addNat (n : Nat) (i : Fin n) : Fin.natAdd n i = i.addNat n := by
  ext
  simp
  omega

theorem rev_castAdd (k : Fin n) (m : Nat) : rev (castAdd m k) = addNat (rev k) m := Fin.ext <| by
  rw [val_rev, coe_castAdd, coe_addNat, val_rev, Nat.sub_add_comm (Nat.succ_le_of_lt k.is_lt)]

theorem rev_addNat (k : Fin n) (m : Nat) : rev (addNat k m) = castAdd m (rev k) := by
  rw [← rev_rev (castAdd ..), rev_castAdd, rev_rev]

theorem rev_castSucc (k : Fin n) : rev (castSucc k) = succ (rev k) := k.rev_castAdd 1

theorem rev_succ (k : Fin n) : rev (succ k) = castSucc (rev k) := k.rev_addNat 1

/-! ### pred -/

@[simp] theorem coe_pred (j : Fin (n + 1)) (h : j ≠ 0) : (j.pred h : Nat) = j - 1 := rfl

@[simp] theorem succ_pred : ∀ (i : Fin (n + 1)) (h : i ≠ 0), (i.pred h).succ = i
  | ⟨0, _⟩, hi => by simp only [mk_zero, ne_eq, not_true] at hi
  | ⟨_ + 1, _⟩, _ => rfl

@[simp]
theorem pred_succ (i : Fin n) {h : i.succ ≠ 0} : i.succ.pred h = i := by
  cases i
  rfl

theorem pred_eq_iff_eq_succ {n : Nat} {i : Fin (n + 1)} (hi : i ≠ 0) {j : Fin n} :
    i.pred hi = j ↔ i = j.succ :=
  ⟨fun h => by simp only [← h, Fin.succ_pred], fun h => by simp only [h, Fin.pred_succ]⟩

theorem pred_mk_succ (i : Nat) (h : i < n + 1) :
    Fin.pred ⟨i + 1, Nat.add_lt_add_right h 1⟩ (ne_of_val_ne (Nat.ne_of_gt (mk_succ_pos i h))) =
      ⟨i, h⟩ := by
  simp only [Fin.ext_iff, coe_pred, Nat.add_sub_cancel]

@[simp] theorem pred_mk_succ' (i : Nat) (h₁ : i + 1 < n + 1 + 1) (h₂) :
    Fin.pred ⟨i + 1, h₁⟩ h₂ = ⟨i, Nat.lt_of_succ_lt_succ h₁⟩ := pred_mk_succ i _

-- This is not a simp theorem by default, because `pred_mk_succ` is nicer when it applies.
theorem pred_mk {n : Nat} (i : Nat) (h : i < n + 1) (w) : Fin.pred ⟨i, h⟩ w =
    ⟨i - 1, Nat.sub_lt_right_of_lt_add (Nat.pos_iff_ne_zero.2 (Fin.val_ne_of_ne w)) h⟩ :=
  rfl

@[simp] theorem pred_le_pred_iff {n : Nat} {a b : Fin n.succ} {ha : a ≠ 0} {hb : b ≠ 0} :
    a.pred ha ≤ b.pred hb ↔ a ≤ b := by rw [← succ_le_succ_iff, succ_pred, succ_pred]

@[simp] theorem pred_lt_pred_iff {n : Nat} {a b : Fin n.succ} {ha : a ≠ 0} {hb : b ≠ 0} :
    a.pred ha < b.pred hb ↔ a < b := by rw [← succ_lt_succ_iff, succ_pred, succ_pred]

@[simp] theorem pred_inj :
    ∀ {a b : Fin (n + 1)} {ha : a ≠ 0} {hb : b ≠ 0}, a.pred ha = b.pred hb ↔ a = b
  | ⟨0, _⟩, _, ha, _ => by simp only [mk_zero, ne_eq, not_true] at ha
  | ⟨i + 1, _⟩, ⟨0, _⟩, _, hb => by simp only [mk_zero, ne_eq, not_true] at hb
  | ⟨i + 1, hi⟩, ⟨j + 1, hj⟩, ha, hb => by simp [Fin.ext_iff, Nat.succ.injEq]

@[simp] theorem pred_one {n : Nat} :
    Fin.pred (1 : Fin (n + 2)) (Ne.symm (Fin.ne_of_lt one_pos)) = 0 := rfl

theorem pred_add_one (i : Fin (n + 2)) (h : (i : Nat) < n + 1) :
    pred (i + 1) (Fin.ne_of_gt (add_one_pos _ (lt_def.2 h))) = castLT i h := by
  rw [Fin.ext_iff, coe_pred, coe_castLT, val_add, val_one, Nat.mod_eq_of_lt, Nat.add_sub_cancel]
  exact Nat.add_lt_add_right h 1

@[simp] theorem coe_subNat (i : Fin (n + m)) (h : m ≤ i) : (i.subNat m h : Nat) = i - m := rfl

@[simp] theorem subNat_mk {i : Nat} (h₁ : i < n + m) (h₂ : m ≤ i) :
    subNat m ⟨i, h₁⟩ h₂ = ⟨i - m, Nat.sub_lt_right_of_lt_add h₂ h₁⟩ := rfl

@[simp] theorem subNat_zero (i : Fin n) (h : 0 ≤ (i : Nat)): Fin.subNat 0 i h = i := by
  ext
  simp

@[simp] theorem subNat_one_succ (i : Fin (n + 1)) (h : 1 ≤ (i : Nat)) : (subNat 1 i h).succ = i := by
  ext
  simp
  omega

@[simp] theorem pred_castSucc_succ (i : Fin n) :
    pred (castSucc i.succ) (Fin.ne_of_gt (castSucc_pos i.succ_pos)) = castSucc i := rfl

@[simp] theorem addNat_subNat {i : Fin (n + m)} (h : m ≤ i) : addNat (subNat m i h) m = i :=
  Fin.ext <| Nat.sub_add_cancel h

@[simp] theorem subNat_addNat (i : Fin n) (m : Nat) (h : m ≤ addNat i m := le_coe_addNat m i) :
    subNat m (addNat i m) h = i := Fin.ext <| Nat.add_sub_cancel i m

@[simp] theorem natAdd_subNat_cast {i : Fin (n + m)} (h : n ≤ i) :
    natAdd n (subNat n (i.cast (Nat.add_comm ..)) h) = i := by simp [← cast_addNat]

/-! ### recursion and induction principles -/

/-- Define `motive n i` by induction on `i : Fin n` interpreted as `(0 : Fin (n - i)).succ.succ…`.
This function has two arguments: `zero n` defines `0`-th element `motive (n+1) 0` of an
`(n+1)`-tuple, and `succ n i` defines `(i+1)`-st element of `(n+1)`-tuple based on `n`, `i`, and
`i`-th element of `n`-tuple. -/
-- FIXME: Performance review
@[elab_as_elim] def succRec {motive : ∀ n, Fin n → Sort _}
    (zero : ∀ n, motive n.succ (0 : Fin (n + 1)))
    (succ : ∀ n i, motive n i → motive n.succ i.succ) : ∀ {n : Nat} (i : Fin n), motive n i
  | 0, i => i.elim0
  | Nat.succ n, ⟨0, _⟩ => by rw [mk_zero]; exact zero n
  | Nat.succ _, ⟨Nat.succ i, h⟩ => succ _ _ (succRec zero succ ⟨i, Nat.lt_of_succ_lt_succ h⟩)

/-- Define `motive n i` by induction on `i : Fin n` interpreted as `(0 : Fin (n - i)).succ.succ…`.
This function has two arguments:
`zero n` defines the `0`-th element `motive (n+1) 0` of an `(n+1)`-tuple, and
`succ n i` defines the `(i+1)`-st element of an `(n+1)`-tuple based on `n`, `i`,
and the `i`-th element of an `n`-tuple.

A version of `Fin.succRec` taking `i : Fin n` as the first argument. -/
-- FIXME: Performance review
@[elab_as_elim] def succRecOn {n : Nat} (i : Fin n) {motive : ∀ n, Fin n → Sort _}
    (zero : ∀ n, motive (n + 1) 0) (succ : ∀ n i, motive n i → motive (Nat.succ n) i.succ) :
    motive n i := i.succRec zero succ

@[simp] theorem succRecOn_zero {motive : ∀ n, Fin n → Sort _} {zero succ} (n) :
    @Fin.succRecOn (n + 1) 0 motive zero succ = zero n := by
  cases n <;> rfl

@[simp] theorem succRecOn_succ {motive : ∀ n, Fin n → Sort _} {zero succ} {n} (i : Fin n) :
    @Fin.succRecOn (n + 1) i.succ motive zero succ = succ n i (Fin.succRecOn i zero succ) := by
  cases i; rfl


/-- Define `motive i` by induction on `i : Fin (n + 1)` via induction on the underlying `Nat` value.
This function has two arguments: `zero` handles the base case on `motive 0`,
and `succ` defines the inductive step using `motive i.castSucc`.
-/
-- FIXME: Performance review
@[elab_as_elim] def induction {motive : Fin (n + 1) → Sort _} (zero : motive 0)
    (succ : ∀ i : Fin n, motive (castSucc i) → motive i.succ) :
    ∀ i : Fin (n + 1), motive i
  | ⟨i, hi⟩ => go i hi
where
  -- Use a curried function so that this is structurally recursive
  go : ∀ (i : Nat) (hi : i < n + 1), motive ⟨i, hi⟩
  | 0, hi => by rwa [Fin.mk_zero]
  | i+1, hi => succ ⟨i, Nat.lt_of_succ_lt_succ hi⟩ (go i (Nat.lt_of_succ_lt hi))

@[simp] theorem induction_zero {motive : Fin (n + 1) → Sort _} (zero : motive 0)
    (hs : ∀ i : Fin n, motive (castSucc i) → motive i.succ) :
    (induction zero hs : ∀ i : Fin (n + 1), motive i) 0 = zero := rfl

@[simp] theorem induction_succ {motive : Fin (n + 1) → Sort _} (zero : motive 0)
    (succ : ∀ i : Fin n, motive (castSucc i) → motive i.succ) (i : Fin n) :
    induction (motive := motive) zero succ i.succ = succ i (induction zero succ (castSucc i)) := rfl

/-- Define `motive i` by induction on `i : Fin (n + 1)` via induction on the underlying `Nat` value.
This function has two arguments: `zero` handles the base case on `motive 0`,
and `succ` defines the inductive step using `motive i.castSucc`.

A version of `Fin.induction` taking `i : Fin (n + 1)` as the first argument.
-/
-- FIXME: Performance review
@[elab_as_elim] def inductionOn (i : Fin (n + 1)) {motive : Fin (n + 1) → Sort _} (zero : motive 0)
    (succ : ∀ i : Fin n, motive (castSucc i) → motive i.succ) : motive i := induction zero succ i

/-- Define `f : Π i : Fin n.succ, motive i` by separately handling the cases `i = 0` and
`i = j.succ`, `j : Fin n`. -/
@[elab_as_elim] def cases {motive : Fin (n + 1) → Sort _}
    (zero : motive 0) (succ : ∀ i : Fin n, motive i.succ) :
    ∀ i : Fin (n + 1), motive i := induction zero fun i _ => succ i

@[simp] theorem cases_zero {n} {motive : Fin (n + 1) → Sort _} {zero succ} :
    @Fin.cases n motive zero succ 0 = zero := rfl

@[simp] theorem cases_succ {n} {motive : Fin (n + 1) → Sort _} {zero succ} (i : Fin n) :
    @Fin.cases n motive zero succ i.succ = succ i := rfl

@[simp] theorem cases_succ' {n} {motive : Fin (n + 1) → Sort _} {zero succ}
    {i : Nat} (h : i + 1 < n + 1) :
    @Fin.cases n motive zero succ ⟨i.succ, h⟩ = succ ⟨i, Nat.lt_of_succ_lt_succ h⟩ := rfl

theorem forall_fin_succ {P : Fin (n + 1) → Prop} : (∀ i, P i) ↔ P 0 ∧ ∀ i : Fin n, P i.succ :=
  ⟨fun H => ⟨H 0, fun _ => H _⟩, fun ⟨H0, H1⟩ i => Fin.cases H0 H1 i⟩

theorem exists_fin_succ {P : Fin (n + 1) → Prop} : (∃ i, P i) ↔ P 0 ∨ ∃ i : Fin n, P i.succ :=
  ⟨fun ⟨i, h⟩ => Fin.cases Or.inl (fun i hi => Or.inr ⟨i, hi⟩) i h, fun h =>
    (h.elim fun h => ⟨0, h⟩) fun ⟨i, hi⟩ => ⟨i.succ, hi⟩⟩

theorem forall_fin_one {p : Fin 1 → Prop} : (∀ i, p i) ↔ p 0 :=
  ⟨fun h => h _, fun h i => Subsingleton.elim i 0 ▸ h⟩

theorem exists_fin_one {p : Fin 1 → Prop} : (∃ i, p i) ↔ p 0 :=
  ⟨fun ⟨i, h⟩ => Subsingleton.elim i 0 ▸ h, fun h => ⟨_, h⟩⟩

theorem forall_fin_two {p : Fin 2 → Prop} : (∀ i, p i) ↔ p 0 ∧ p 1 :=
  forall_fin_succ.trans <| and_congr_right fun _ => forall_fin_one

theorem exists_fin_two {p : Fin 2 → Prop} : (∃ i, p i) ↔ p 0 ∨ p 1 :=
  exists_fin_succ.trans <| or_congr_right exists_fin_one

theorem fin_two_eq_of_eq_zero_iff : ∀ {a b : Fin 2}, (a = 0 ↔ b = 0) → a = b := by
  simp only [forall_fin_two]; decide

/--
Define `motive i` by reverse induction on `i : Fin (n + 1)` via induction on the underlying `Nat`
value. This function has two arguments: `last` handles the base case on `motive (Fin.last n)`,
and `cast` defines the inductive step using `motive i.succ`, inducting downwards.
-/
@[elab_as_elim] def reverseInduction {motive : Fin (n + 1) → Sort _} (last : motive (Fin.last n))
    (cast : ∀ i : Fin n, motive i.succ → motive (castSucc i)) (i : Fin (n + 1)) : motive i :=
  if hi : i = Fin.last n then _root_.cast (congrArg motive hi.symm) last
  else
    let j : Fin n := ⟨i, Nat.lt_of_le_of_ne (Nat.le_of_lt_succ i.2) fun h => hi (Fin.ext h)⟩
    cast _ (reverseInduction last cast j.succ)
termination_by n + 1 - i
decreasing_by decreasing_with
  -- FIXME: we put the proof down here to avoid getting a dummy `have` in the definition
  try simp only [Nat.succ_sub_succ_eq_sub]
  exact Nat.add_sub_add_right .. ▸ Nat.sub_lt_sub_left i.2 (Nat.lt_succ_self i)

@[simp] theorem reverseInduction_last {n : Nat} {motive : Fin (n + 1) → Sort _} {zero succ} :
    (reverseInduction zero succ (Fin.last n) : motive (Fin.last n)) = zero := by
  rw [reverseInduction]; simp

@[simp] theorem reverseInduction_castSucc {n : Nat} {motive : Fin (n + 1) → Sort _} {zero succ}
    (i : Fin n) : reverseInduction (motive := motive) zero succ (castSucc i) =
      succ i (reverseInduction zero succ i.succ) := by
  rw [reverseInduction, dif_neg (Fin.ne_of_lt (Fin.castSucc_lt_last i))]; rfl

/-- Define `f : Π i : Fin n.succ, motive i` by separately handling the cases `i = Fin.last n` and
`i = j.castSucc`, `j : Fin n`. -/
@[elab_as_elim] def lastCases {n : Nat} {motive : Fin (n + 1) → Sort _} (last : motive (Fin.last n))
    (cast : ∀ i : Fin n, motive (castSucc i)) (i : Fin (n + 1)) : motive i :=
  reverseInduction last (fun i _ => cast i) i

@[simp] theorem lastCases_last {n : Nat} {motive : Fin (n + 1) → Sort _} {last cast} :
    (Fin.lastCases last cast (Fin.last n) : motive (Fin.last n)) = last :=
  reverseInduction_last ..

@[simp] theorem lastCases_castSucc {n : Nat} {motive : Fin (n + 1) → Sort _} {last cast}
    (i : Fin n) : (Fin.lastCases last cast (Fin.castSucc i) : motive (Fin.castSucc i)) = cast i :=
  reverseInduction_castSucc ..

/-- Define `f : Π i : Fin (m + n), motive i` by separately handling the cases `i = castAdd n i`,
`j : Fin m` and `i = natAdd m j`, `j : Fin n`. -/
@[elab_as_elim] def addCases {m n : Nat} {motive : Fin (m + n) → Sort u}
    (left : ∀ i, motive (castAdd n i)) (right : ∀ i, motive (natAdd m i))
    (i : Fin (m + n)) : motive i :=
  if hi : (i : Nat) < m then (castAdd_castLT n i hi) ▸ (left (castLT i hi))
  else (natAdd_subNat_cast (Nat.le_of_not_lt hi)) ▸ (right _)

@[simp] theorem addCases_left {m n : Nat} {motive : Fin (m + n) → Sort _} {left right} (i : Fin m) :
    addCases (motive := motive) left right (Fin.castAdd n i) = left i := by
  rw [addCases, dif_pos (castAdd_lt _ _)]; rfl

@[simp]
theorem addCases_right {m n : Nat} {motive : Fin (m + n) → Sort _} {left right} (i : Fin n) :
    addCases (motive := motive) left right (natAdd m i) = right i := by
  have : ¬(natAdd m i : Nat) < m := Nat.not_lt.2 (le_coe_natAdd ..)
  rw [addCases, dif_neg this]; exact eq_of_heq <| (eqRec_heq _ _).trans (by congr 1; simp)

/-! ### add -/

theorem ofNat'_add [NeZero n] (x : Nat) (y : Fin n) :
    Fin.ofNat' n x + y = Fin.ofNat' n (x + y.val) := by
  apply Fin.eq_of_val_eq
  simp [Fin.ofNat', Fin.add_def]

theorem add_ofNat' [NeZero n] (x : Fin n) (y : Nat) :
    x + Fin.ofNat' n y = Fin.ofNat' n (x.val + y) := by
  apply Fin.eq_of_val_eq
  simp [Fin.ofNat', Fin.add_def]

/-! ### sub -/

protected theorem coe_sub (a b : Fin n) : ((a - b : Fin n) : Nat) = ((n - b) + a) % n := by
  cases a; cases b; rfl

theorem ofNat'_sub [NeZero n] (x : Nat) (y : Fin n) :
    Fin.ofNat' n x - y = Fin.ofNat' n ((n - y.val) + x) := by
  apply Fin.eq_of_val_eq
  simp [Fin.ofNat', Fin.sub_def]

theorem sub_ofNat' [NeZero n] (x : Fin n) (y : Nat) :
    x - Fin.ofNat' n y = Fin.ofNat' n ((n - y % n) + x.val) := by
  apply Fin.eq_of_val_eq
  simp [Fin.ofNat', Fin.sub_def]

@[simp] protected theorem sub_self [NeZero n] {x : Fin n} : x - x = 0 := by
  ext
  rw [Fin.sub_def]
  simp

private theorem _root_.Nat.mod_eq_sub_of_lt_two_mul {x n} (h₁ : n ≤ x) (h₂ : x < 2 * n) :
    x % n = x - n := by
  rw [Nat.mod_eq, if_pos (by omega), Nat.mod_eq_of_lt (by omega)]

theorem coe_sub_iff_le {a b : Fin n} : (↑(a - b) : Nat) = a - b ↔ b ≤ a := by
  rw [sub_def, le_def]
  dsimp only
  if h : n ≤ (n - b) + a then
    rw [Nat.mod_eq_sub_of_lt_two_mul h]
    all_goals omega
  else
    rw [Nat.mod_eq_of_lt]
    all_goals omega

theorem sub_val_of_le {a b : Fin n} : b ≤ a → (a - b).val = a.val - b.val :=
  coe_sub_iff_le.2

theorem coe_sub_iff_lt {a b : Fin n} : (↑(a - b) : Nat) = n + a - b ↔ a < b := by
  rw [sub_def, lt_def]
  dsimp only
  if h : n ≤ (n - b) + a then
    rw [Nat.mod_eq_sub_of_lt_two_mul h]
    all_goals omega
  else
    rw [Nat.mod_eq_of_lt]
    all_goals omega

/-! ### mul -/

theorem val_mul {n : Nat} : ∀ a b : Fin n, (a * b).val = a.val * b.val % n
  | ⟨_, _⟩, ⟨_, _⟩ => rfl

theorem coe_mul {n : Nat} : ∀ a b : Fin n, ((a * b : Fin n) : Nat) = a * b % n
  | ⟨_, _⟩, ⟨_, _⟩ => rfl

protected theorem mul_one (k : Fin (n + 1)) : k * 1 = k := by
  match n with
  | 0 => exact Subsingleton.elim (α := Fin 1) ..
  | n+1 => simp [Fin.ext_iff, mul_def, Nat.mod_eq_of_lt (is_lt k)]

protected theorem mul_comm (a b : Fin n) : a * b = b * a :=
  Fin.ext <| by rw [mul_def, mul_def, Nat.mul_comm]
instance : Std.Commutative (α := Fin n) (· * ·) := ⟨Fin.mul_comm⟩

protected theorem mul_assoc (a b c : Fin n) : a * b * c = a * (b * c) := by
  apply eq_of_val_eq
  simp only [val_mul]
  rw [← Nat.mod_eq_of_lt a.isLt, ← Nat.mod_eq_of_lt b.isLt, ← Nat.mod_eq_of_lt c.isLt]
  simp only [← Nat.mul_mod, Nat.mul_assoc]
instance : Std.Associative (α := Fin n) (· * ·) := ⟨Fin.mul_assoc⟩

protected theorem one_mul (k : Fin (n + 1)) : (1 : Fin (n + 1)) * k = k := by
  rw [Fin.mul_comm, Fin.mul_one]
instance : Std.LawfulIdentity (α := Fin (n + 1)) (· * ·) 1 where
  left_id := Fin.one_mul
  right_id := Fin.mul_one

protected theorem mul_zero (k : Fin (n + 1)) : k * 0 = 0 := by simp [Fin.ext_iff, mul_def]

protected theorem zero_mul (k : Fin (n + 1)) : (0 : Fin (n + 1)) * k = 0 := by
  simp [Fin.ext_iff, mul_def]

end Fin
