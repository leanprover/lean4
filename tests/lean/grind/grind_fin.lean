/-!
Currently failing examples for `grind`.
Many of these will remain out of scope, and can be deleted as this is decided.
-/

/-! Works with `grind ext`. -/

attribute [grind ext] Fin.ext

theorem rev_eq {n a : Nat} (i : Fin (n + 1)) (h : n = a + i) :
    rev i = ⟨a, Nat.lt_succ_of_le (h ▸ Nat.le_add_right ..)⟩ := by grind

theorem castLE_succ {m n : Nat} (h : m + 1 ≤ n + 1) (i : Fin m) :
    castLE h i.succ = (castLE (Nat.succ_le_succ_iff.mp h) i).succ := by grind

theorem cast_last {n' : Nat} {h : n + 1 = n' + 1} : (last n).cast h  = last n' := by grind

theorem castAdd_zero : (castAdd 0 : Fin n → Fin (n + 0)) = Fin.cast rfl := by grind

theorem castAdd_mk (m : Nat) (i : Nat) (h : i < n) :
    castAdd m ⟨i, h⟩ = ⟨i, Nat.lt_add_right m h⟩ := by grind

theorem castAdd_castLT (m : Nat) (i : Fin (n + m)) (hi : i.val < n) :
    castAdd m (castLT i hi) = i := by grind

theorem castAdd_cast {n n' : Nat} (m : Nat) (i : Fin n') (h : n' = n) :
    castAdd m (Fin.cast h i) = Fin.cast (congrArg (. + m) h) (castAdd m i) := by grind

theorem cast_castAdd_left {n n' m : Nat} (i : Fin n') (h : n' + m = n + m) :
    (i.castAdd m).cast h = (i.cast (Nat.add_right_cancel h)).castAdd m := by grind

theorem cast_castAdd_right {n m m' : Nat} (i : Fin n) (h : n + m' = n + m) :
    (i.castAdd m').cast h = i.castAdd m := by grind

theorem castAdd_castAdd {m n p : Nat} (i : Fin m) :
    (i.castAdd n).castAdd p = (i.castAdd (n + p)).cast (Nat.add_assoc ..).symm := by grind

theorem cast_succ_eq {n' : Nat} (i : Fin n) (h : n.succ = n'.succ) :
    i.succ.cast h = (i.cast (Nat.succ.inj h)).succ := by grind

theorem succ_cast_eq {n' : Nat} (i : Fin n) (h : n = n') :
    (i.cast h).succ = i.succ.cast (by rw [h]) := by grind

theorem castSucc_mk (n i : Nat) (h : i < n) : castSucc ⟨i, h⟩ = ⟨i, Nat.lt_succ_of_lt h⟩ := by grind

theorem cast_castSucc {n' : Nat} {h : n + 1 = n' + 1} {i : Fin n} :
    i.castSucc.cast h = (i.cast (Nat.succ.inj h)).castSucc := by grind

theorem castSucc_castLT (i : Fin (n + 1)) (h : (i : Nat) < n) :
    (castLT i h).castSucc = i := by grind

theorem addNat_zero (n : Nat) (i : Fin n) : addNat i 0 = i := by grind

theorem addNat_one {i : Fin n} : addNat i 1 = i.succ := by grind

theorem addNat_mk (n i : Nat) (hi : i < m) :
    addNat ⟨i, hi⟩ n = ⟨i + n, Nat.add_lt_add_right hi n⟩ := by grind

theorem addNat_cast {n n' m : Nat} (i : Fin n') (h : n' = n) :
    addNat (i.cast h) m = (addNat i m).cast (congrArg (. + m) h) := by grind

theorem cast_addNat_left {n n' m : Nat} (i : Fin n') (h : n' + m = n + m) :
    (addNat i m).cast h = addNat (i.cast (Nat.add_right_cancel h)) m := by grind

theorem cast_addNat_right {n m m' : Nat} (i : Fin n) (h : n + m' = n + m) :
    (addNat i m').cast h = addNat i m := by grind

theorem natAdd_mk (n i : Nat) (hi : i < m) :
    natAdd n ⟨i, hi⟩ = ⟨n + i, Nat.add_lt_add_left hi n⟩ := by grind

theorem natAdd_zero {n : Nat} : natAdd 0 = Fin.cast (Nat.zero_add n).symm := by grind

theorem natAdd_cast {n n' : Nat} (m : Nat) (i : Fin n') (h : n' = n) :
    natAdd m (i.cast h) = (natAdd m i).cast (congrArg _ h) := by grind

theorem cast_natAdd_right {n n' m : Nat} (i : Fin n') (h : m + n' = m + n) :
    (natAdd m i).cast h  = natAdd m (i.cast (Nat.add_left_cancel h)) := by grind

theorem cast_natAdd_left {n m m' : Nat} (i : Fin n) (h : m' + n = m + n) :
    (natAdd m' i).cast h = natAdd m i := by grind

theorem castAdd_natAdd (p m : Nat) {n : Nat} (i : Fin n) :
    castAdd p (natAdd m i) = (natAdd m (castAdd p i)).cast (Nat.add_assoc ..).symm := by grind

theorem natAdd_castAdd (p m : Nat) {n : Nat} (i : Fin n) :
    natAdd m (castAdd p i) = (castAdd p (natAdd m i)).cast (Nat.add_assoc ..) := by grind

theorem natAdd_natAdd (m n : Nat) {p : Nat} (i : Fin p) :
    natAdd m (natAdd n i) = (natAdd (m + n) i).cast (Nat.add_assoc ..) := by grind

theorem cast_natAdd (n : Nat) {m : Nat} (i : Fin m) :
    (natAdd n i).cast (Nat.add_comm ..) = addNat i n := by grind

theorem cast_addNat {n : Nat} (m : Nat) (i : Fin n) :
    (addNat i m).cast (Nat.add_comm ..) = natAdd m i := by grind

theorem natAdd_last {m n : Nat} : natAdd n (last m) = last (n + m) := by grind

theorem addNat_last (n : Nat) :
    addNat (last n) m = (last (n + m)).cast (by omega) := by grind

theorem natAdd_eq_addNat (n : Nat) (i : Fin n) : Fin.natAdd n i = i.addNat n := by grind

theorem rev_castAdd (k : Fin n) (m : Nat) : rev (castAdd m k) = addNat (rev k) m := by grind

theorem rev_addNat (k : Fin n) (m : Nat) : rev (addNat k m) = castAdd m (rev k) := by grind

theorem rev_succ (k : Fin n) : rev (succ k) = castSucc (rev k) := by grind

theorem pred_mk_succ (i : Nat) (h : i < n + 1) :
    Fin.pred ⟨i + 1, Nat.add_lt_add_right h 1⟩ (ne_of_val_ne (Nat.ne_of_gt (mk_succ_pos i h))) =
      ⟨i, h⟩ := by grind

theorem pred_mk_succ' (i : Nat) (h₁ : i + 1 < n + 1 + 1) (h₂) :
    Fin.pred ⟨i + 1, h₁⟩ h₂ = ⟨i, Nat.lt_of_succ_lt_succ h₁⟩ := by grind
theorem addNat_subNat {i : Fin (n + m)} (h : m ≤ i) : addNat (subNat m i h) m = i := by grind

theorem natAdd_subNat_cast {i : Fin (n + m)} (h : n ≤ i) :
    natAdd n (subNat n (i.cast (Nat.add_comm ..)) h) = i := by grind

theorem sub_ofNat [NeZero n] (x : Fin n) (y : Nat) :
    x - Fin.ofNat n y = Fin.ofNat n ((n - y % n) + x.val) := by grind

theorem succ_mk (n i : Nat) (h : i < n) :
    Fin.succ ⟨i, h⟩ = ⟨i + 1, Nat.succ_lt_succ h⟩ := by grind

/-! These could work, but need additional help from `grind`, because these annotations are bad: -/
attribute [grind =] Fin.val_zero Fin.val_one Fin.le_def Fin.lt_def

theorem val_zero (n : Nat) [NeZero n] : ((0 : Fin n) : Nat) = 0 := by grind

theorem mk_zero : (⟨0, Nat.succ_pos n⟩ : Fin (n + 1)) = 0 := by grind

theorem zero_le [NeZero n] (a : Fin n) : 0 ≤ a := by grind

theorem zero_lt_one : (0 : Fin (n + 2)) < 1 := by grind

theorem not_lt_zero [NeZero n] (a : Fin n) : ¬a < 0 := by grind

theorem pos_iff_ne_zero [NeZero n] {a : Fin n} : 0 < a ↔ a ≠ 0 := by grind

theorem zero_eq_last_iff {n : Nat} : (0 : Fin (n + 1)) = last n ↔ n = 0 := by grind

theorem last_eq_zero_iff {n : Nat} : Fin.last n = 0 ↔ n = 0 := by grind

theorem last_pos : (0 : Fin (n + 2)) < last (n + 1) := by grind

theorem rev_last (n : Nat) : rev (last n) = 0 := by grind

theorem rev_zero (n : Nat) : rev 0 = last n := by grind

theorem val_one (n : Nat) : (1 : Fin (n + 2)).val = 1 := by grind

theorem mk_one : (⟨1, Nat.succ_lt_succ (Nat.succ_pos n)⟩ : Fin (n + 2)) = (1 : Fin _) := by grind

theorem succ_pos (a : Fin n) : (0 : Fin (n + 1)) < a.succ := by grind

theorem succ_ne_zero {n} : ∀ k : Fin n, Fin.succ k ≠ 0 := by grind

theorem succ_zero_eq_one : Fin.succ (0 : Fin (n + 1)) = 1 := by grind

theorem mk_succ_pos (i : Nat) (h : i < n) :
    (0 : Fin (n + 1)) < ⟨i.succ, Nat.add_lt_add_right h 1⟩ := by grind

theorem one_lt_succ_succ (a : Fin n) : (1 : Fin (n + 2)) < a.succ.succ := by grind

theorem le_zero_iff {n : Nat} {k : Fin (n + 1)} : k ≤ 0 ↔ k = 0 := by grind

theorem succ_succ_ne_one (a : Fin n) : Fin.succ (Fin.succ a) ≠ 1 := by grind

theorem castLE_zero {n m : Nat} (h : n.succ ≤ m.succ) : castLE h 0 = 0 := by grind

theorem castSucc_lt_succ {i : Fin n} : i.castSucc < i.succ := by grind

theorem le_castSucc_iff {i : Fin (n + 1)} {j : Fin n} : i ≤ j.castSucc ↔ i < j.succ := by grind

theorem castSucc_lt_iff_succ_le {n : Nat} {i : Fin n} {j : Fin (n + 1)} :
    i.castSucc < j ↔ i.succ ≤ j := by grind

theorem castSucc_lt_castSucc_iff {a b : Fin n} :
    a.castSucc < b.castSucc ↔ a < b := by grind

theorem castSucc_lt_last (a : Fin n) : a.castSucc < last n := by grind

theorem castSucc_zero [NeZero n] : castSucc (0 : Fin n) = 0 := by grind

theorem castSucc_one {n : Nat} : castSucc (1 : Fin (n + 2)) = 1 := by grind

theorem castSucc_pos [NeZero n] {i : Fin n} (h : 0 < i) : 0 < i.castSucc := by grind

theorem castSucc_succ (i : Fin n) : i.succ.castSucc = i.castSucc.succ := by grind

theorem succ_pred : ∀ (i : Fin (n + 1)) (h : i ≠ 0), (i.pred h).succ = i := by grind

theorem pred_eq_iff_eq_succ {n : Nat} {i : Fin (n + 1)} (hi : i ≠ 0) {j : Fin n} :
    i.pred hi = j ↔ i = j.succ := by grind

theorem pred_le_pred_iff {n : Nat} {a b : Fin n.succ} {ha : a ≠ 0} {hb : b ≠ 0} :
    a.pred ha ≤ b.pred hb ↔ a ≤ b := by grind

theorem pred_lt_pred_iff {n : Nat} {a b : Fin n.succ} {ha : a ≠ 0} {hb : b ≠ 0} :
    a.pred ha < b.pred hb ↔ a < b := by grind

theorem pred_inj :
    ∀ {a b : Fin (n + 1)} {ha : a ≠ 0} {hb : b ≠ 0}, a.pred ha = b.pred hb ↔ a = b := by grind

theorem pred_one {n : Nat} :
    Fin.pred (1 : Fin (n + 2)) (Ne.symm (Fin.ne_of_lt zero_lt_one)) = 0 := by grind

theorem val_eq_zero_iff [NeZero n] {a : Fin n} : a.val = 0 ↔ a = 0 := by grind

theorem val_ne_zero_iff [NeZero n] {a : Fin n} : a.val ≠ 0 ↔ a ≠ 0 := by grind

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
