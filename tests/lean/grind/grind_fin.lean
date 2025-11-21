/-!
Currently failing examples for `grind`.
Many of these will remain out of scope, and can be deleted as this is decided.
-/

theorem ofNat_zero (n : Nat) [NeZero n] : Fin.ofNat n 0 = 0 := by grind

theorem mod_def (a m : Fin n) :
    a % m = Fin.mk (a.val % m.val) (Nat.lt_of_le_of_lt (Nat.mod_le _ _) a.2) := by grind

theorem mul_def (a b : Fin n) : a * b = Fin.mk ((a.val * b.val) % n) (Nat.mod_lt _ a.pos) := by grind

theorem sub_def (a b : Fin n) : a - b = Fin.mk (((n - b.val) + a.val) % n) (Nat.mod_lt _ a.pos) := by grind

theorem pos' [Nonempty (Fin n)] : 0 < n := by grind

theorem eq_mk_iff_val_eq {a : Fin n} {k : Nat} {hk : k < n} :
    a = ⟨k, hk⟩ ↔ (a : Nat) = k := by grind

theorem ofNat_self {n : Nat} [NeZero n] : Fin.ofNat n n = 0 := by grind

theorem ofNat_val_eq_self [NeZero n] (x : Fin n) : (Fin.ofNat n x.val) = x := by
  -- mod_eq_of_lt might be plausible for the implication gadget?
  grind [Nat.mod_eq_of_lt]

theorem modn_val (a : Fin n) (b : Nat) : (a.modn b).val = a.val % b := by grind

theorem mk_lt_of_lt_val {b : Fin n} {a : Nat} (h : a < b) :
    (⟨a, Nat.lt_trans h b.is_lt⟩ : Fin n) < b := by grind

theorem mk_le_of_le_val {b : Fin n} {a : Nat} (h : a ≤ b) :
    (⟨a, Nat.lt_of_le_of_lt h b.is_lt⟩ : Fin n) ≤ b := by grind

theorem mk_le_mk {x y : Nat} {hx hy} : (⟨x, hx⟩ : Fin n) ≤ ⟨y, hy⟩ ↔ x ≤ y := by grind

theorem mk_lt_mk {x y : Nat} {hx hy} : (⟨x, hx⟩ : Fin n) < ⟨y, hy⟩ ↔ x < y := by grind

theorem val_last (n : Nat) : (last n).1 = n := by grind

theorem add_def (a b : Fin n) : a + b = Fin.mk ((a + b) % n) (Nat.mod_lt _ a.pos) := by grind

theorem coe_castLT (i : Fin m) (h : i.1 < n) : (castLT i h : Nat) = i := by grind

theorem castLT_mk (i n m : Nat) (hn : i < n) (hm : i < m) : castLT ⟨i, hn⟩ hm = ⟨i, hm⟩ := by grind

theorem castLE_mk (i n m : Nat) (hn : i < n) (h : n ≤ m) :
    castLE h ⟨i, hn⟩ = ⟨i, Nat.lt_of_lt_of_le hn h⟩ := by grind

theorem castLE_castLE {k m n} (km : k ≤ m) (mn : m ≤ n) (i : Fin k) :
    Fin.castLE mn (Fin.castLE km i) = Fin.castLE (Nat.le_trans km mn) i := by grind

theorem castLE_comp_castLE {k m n} (km : k ≤ m) (mn : m ≤ n) :
    Fin.castLE mn ∘ Fin.castLE km = Fin.castLE (Nat.le_trans km mn) := by grind

theorem coe_cast (h : n = m) (i : Fin n) : (i.cast h : Nat) = i := by grind

theorem cast_castLE {k m n} (km : k ≤ m) (mn : m = n) (i : Fin k) :
    Fin.cast mn (i.castLE km) = i.castLE (mn ▸ km) := by grind

theorem cast_castLT {k m n} (i : Fin k) (h : (i : Nat) < m) (mn : m = n) :
    Fin.cast mn (i.castLT h) = i.castLT (mn ▸ h) := by grind

theorem cast_zero [NeZero n] [NeZero m] (h : n = m) : Fin.cast h 0 = 0 := by grind

theorem cast_mk (h : n = m) (i : Nat) (hn : i < n) : Fin.cast h ⟨i, hn⟩ = ⟨i, h ▸ hn⟩ := by grind

theorem cast_refl (n : Nat) (h : n = n) : Fin.cast h = id := by grind

theorem castLE_of_eq {m n : Nat} (h : m = n) {h' : m ≤ n} : castLE h' = Fin.cast h := by grind

theorem coe_castAdd (m : Nat) (i : Fin n) : (castAdd m i : Nat) = i := by grind

theorem castAdd_lt {m : Nat} (n : Nat) (i : Fin m) : (castAdd n i : Nat) < m := by grind

theorem castLT_castAdd (m : Nat) (i : Fin n) :
    castLT (castAdd m i) (castAdd_lt m i) = i := by grind

theorem coe_castSucc (i : Fin n) : (i.castSucc : Nat) = i := by grind

theorem succ_last (n : Nat) : (last n).succ = last n.succ := by grind

theorem succ_eq_last_succ {n : Nat} {i : Fin n.succ} :
    i.succ = last (n + 1) ↔ i = last n := by grind

theorem castLT_castSucc {n : Nat} (a : Fin n) (h : (a : Nat) < n) :
    castLT a.castSucc h = a := by grind

theorem coe_addNat (m : Nat) (i : Fin n) : (addNat i m : Nat) = i + m := by grind

theorem le_coe_addNat (m : Nat) (i : Fin n) : m ≤ addNat i m := by grind

theorem cast_addNat_zero {n n' : Nat} (i : Fin n) (h : n + 0 = n') :
    (addNat i 0).cast h = i.cast ((Nat.add_zero _).symm.trans h) := by grind

theorem rev_castSucc (k : Fin n) : rev (castSucc k) = succ (rev k) := by grind

theorem coe_pred (j : Fin (n + 1)) (h : j ≠ 0) : (j.pred h : Nat) = j - 1 := by grind

theorem pred_succ (i : Fin n) {h : i.succ ≠ 0} : i.succ.pred h = i := by grind

theorem cast_natAdd_zero {n n' : Nat} (i : Fin n) (h : 0 + n = n') :
    (natAdd 0 i).cast h = i.cast ((Nat.zero_add _).symm.trans h) := by grind

theorem pred_mk {n : Nat} (i : Nat) (h : i < n + 1) (w) : Fin.pred ⟨i, h⟩ w =
    ⟨i - 1, Nat.sub_lt_right_of_lt_add (Nat.pos_iff_ne_zero.2 (Fin.val_ne_of_ne w)) h⟩ := by grind

theorem coe_subNat (i : Fin (n + m)) (h : m ≤ i) : (i.subNat m h : Nat) = i - m := by grind

theorem subNat_mk {i : Nat} (h₁ : i < n + m) (h₂ : m ≤ i) :
    subNat m ⟨i, h₁⟩ h₂ = ⟨i - m, Nat.sub_lt_right_of_lt_add h₂ h₁⟩ := by grind

theorem subNat_zero (i : Fin n) (h : 0 ≤ (i : Nat)): Fin.subNat 0 i h = i := by grind

theorem subNat_one_succ (i : Fin (n + 1)) (h : 1 ≤ (i : Nat)) : (subNat 1 i h).succ = i := by grind

theorem pred_castSucc_succ (i : Fin n) :
    pred (castSucc i.succ) (Fin.ne_of_gt (castSucc_pos i.succ_pos)) = castSucc i := by grind

theorem subNat_addNat (i : Fin n) (m : Nat) (h : m ≤ addNat i m := le_coe_addNat m i) :
    subNat m (addNat i m) h = i := by grind

theorem succRecOn_zero {motive : ∀ n, Fin n → Sort _} {zero succ} (n) :
    @Fin.succRecOn (n + 1) 0 motive zero succ = zero n := by grind

theorem succRecOn_succ {motive : ∀ n, Fin n → Sort _} {zero succ} {n} (i : Fin n) :
    @Fin.succRecOn (n + 1) i.succ motive zero succ = succ n i (Fin.succRecOn i zero succ) := by grind

theorem induction_zero {motive : Fin (n + 1) → Sort _} (zero : motive 0)
    (hs : ∀ i : Fin n, motive (castSucc i) → motive i.succ) :
    (induction zero hs : ∀ i : Fin (n + 1), motive i) 0 = zero := by grind

theorem induction_succ {motive : Fin (n + 1) → Sort _} (zero : motive 0)
    (succ : ∀ i : Fin n, motive (castSucc i) → motive i.succ) (i : Fin n) :
    induction (motive := motive) zero succ i.succ = succ i (induction zero succ (castSucc i)) := by grind

theorem cases_zero {n} {motive : Fin (n + 1) → Sort _} {zero succ} :
    @Fin.cases n motive zero succ 0 = zero := by grind

theorem cases_succ {n} {motive : Fin (n + 1) → Sort _} {zero succ} (i : Fin n) :
    @Fin.cases n motive zero succ i.succ = succ i := by grind

theorem cases_succ' {n} {motive : Fin (n + 1) → Sort _} {zero succ}
    {i : Nat} (h : i + 1 < n + 1) :
    @Fin.cases n motive zero succ ⟨i.succ, h⟩ = succ ⟨i, Nat.lt_of_succ_lt_succ h⟩ := by grind

theorem reverseInduction_last {n : Nat} {motive : Fin (n + 1) → Sort _} {zero succ} :
    (reverseInduction zero succ (Fin.last n) : motive (Fin.last n)) = zero := by grind

theorem reverseInduction_castSucc {n : Nat} {motive : Fin (n + 1) → Sort _} {zero succ}
    (i : Fin n) : reverseInduction (motive := motive) zero succ (castSucc i) =
      succ i (reverseInduction zero succ i.succ) := by grind

theorem lastCases_last {n : Nat} {motive : Fin (n + 1) → Sort _} {last cast} :
    (Fin.lastCases last cast (Fin.last n) : motive (Fin.last n)) = last := by grind

theorem lastCases_castSucc {n : Nat} {motive : Fin (n + 1) → Sort _} {last cast}
    (i : Fin n) : (Fin.lastCases last cast (Fin.castSucc i) : motive (Fin.castSucc i)) = cast i := by grind

theorem addCases_left {m n : Nat} {motive : Fin (m + n) → Sort _} {left right} (i : Fin m) :
    addCases (motive := motive) left right (Fin.castAdd n i) = left i := by grind

theorem addCases_right {m n : Nat} {motive : Fin (m + n) → Sort _} {left right} (i : Fin n) :
    addCases (motive := motive) left right (natAdd m i) = right i := by grind

theorem val_neg {n : Nat} [NeZero n] (x : Fin n) :
    (-x).val = if x = 0 then 0 else n - x.val := by grind

theorem coe_sub (a b : Fin n) : ((a - b : Fin n) : Nat) = ((n - b) + a) % n := by grind

theorem val_mul {n : Nat} : ∀ a b : Fin n, (a * b).val = a.val * b.val % n
  | ⟨_, _⟩, ⟨_, _⟩ => by grind

theorem le_last (i : Fin (n + 1)) : i ≤ last n := by grind

theorem eq_last_of_not_lt {i : Fin (n + 1)} (h : ¬(i : Nat) < n) : i = last n := by grind

theorem val_lt_last {i : Fin (n + 1)} : i ≠ last n → (i : Nat) < n := by grind

theorem val_succ (j : Fin n) : (j.succ : Nat) = j + 1 := by grind

theorem succ_le_succ_iff {a b : Fin n} : a.succ ≤ b.succ ↔ a ≤ b := by grind

theorem succ_lt_succ_iff {a b : Fin n} : a.succ < b.succ ↔ a < b := by grind

theorem succ_inj {a b : Fin n} : a.succ = b.succ ↔ a = b := by grind

theorem coe_natAdd (n : Nat) {m : Nat} (i : Fin m) : (natAdd n i : Nat) = n + i := by grind

theorem le_coe_natAdd (m : Nat) (i : Fin n) : m ≤ natAdd m i := by grind

theorem last_le_iff {n : Nat} {k : Fin (n + 1)} : last n ≤ k ↔ k = last n := by grind

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
