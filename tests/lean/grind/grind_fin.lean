/-!
Currently failing examples for `grind`.
Many of these will remain out of scope, and can be deleted as this is decided.
-/

open Fin

example (n : Nat) [NeZero n] : Fin.ofNat n 0 = 0 := by grind

example {n a : Nat} {ha : a < n} [NeZero n] :
    (⟨a, ha⟩ : Fin n) = 0 ↔ a = 0 := by grind

example {n : Nat} [NeZero n] : Fin.ofNat n n = 0 := by grind

example [NeZero n] (x : Fin n) : (Fin.ofNat n x.val) = x := by grind

example (a : Fin (2 * n + 1)) : a.val + (-a).val = 2 * n + 1 := by grind

example [NeZero n] {a : Fin n} : 0 < a ↔ a ≠ 0 := by grind

example (i : Fin n) : rev (rev i) = i := by grind

example {i j : Fin n} : rev i ≤ rev j ↔ j ≤ i := by grind

example {i j : Fin n} : rev i = rev j ↔ i = j := by grind

example (n : Nat) : (last n).1 = n := by grind

example {n : Nat} : (0 : Fin (n + 1)) = last n ↔ n = 0 := by grind

example {n : Nat} : Fin.last n = 0 ↔ n = 0 := by grind

example (i : Fin (n + 1)) : i ≤ last n := by grind

example : (0 : Fin (n + 2)) < last (n + 1) := by grind

example {i : Fin (n + 1)} (h : ¬(i : Nat) < n) : i = last n := by grind

example {i : Fin (n + 1)} : i ≠ last n → (i : Nat) < n := by grind

example (n : Nat) : rev (last n) = 0 := by grind

example (n : Nat) : rev 0 = last n := by grind

example {n : Nat} : (2 : Fin (n + 3)).val = 2 := by grind
example {n : Nat} : (17 : Fin (n + 18)).val = 17 := by grind

example : (0 : Fin (n + 2)) < 1 := by grind

example (j : Fin n) : (j.succ : Nat) = j + 1 := by grind

example (a : Fin n) : (0 : Fin (n + 1)) < a.succ := by grind

example {a b : Fin n} : a.succ ≤ b.succ ↔ a ≤ b := by grind

example {a b : Fin n} : a.succ < b.succ ↔ a < b := by grind

example {a b : Fin n} : a.succ = b.succ ↔ a = b := by grind

example {n} : ∀ k : Fin n, Fin.succ k ≠ 0 := by grind

example {n : Nat} {k : Fin (n + 2)} : k + 1 < k ↔ k = last _ := by grind

example {n : Nat} : ∀ {k : Fin (n + 1)}, k + 1 ≤ k ↔ k = last _ := by grind

example {n : Nat} {k : Fin (n + 1)} : last n ≤ k ↔ k = last n := by grind

example {n : Nat} {k : Fin (n + 1)} : k < k + 1 ↔ k < last n := by grind

example (i : Fin m) (h : i.1 < n) : (castLT i h : Nat) = i := by grind

example (i n m : Nat) (hn : i < n) (hm : i < m) : castLT ⟨i, hn⟩ hm = ⟨i, hm⟩ := by grind

example (i n m : Nat) (hn : i < n) (h : n ≤ m) :
    castLE h ⟨i, hn⟩ = ⟨i, Nat.lt_of_lt_of_le hn h⟩ := by grind

example {n m : Nat} (h : n.succ ≤ m.succ) : castLE h 0 = 0 := by grind

example {m n : Nat} (h : m + 1 ≤ n + 1) (i : Fin m) :
    castLE h i.succ = (castLE (Nat.succ_le_succ_iff.mp h) i).succ := by grind

example {k m n} (km : k ≤ m) (mn : m ≤ n) (i : Fin k) :
    Fin.castLE mn (Fin.castLE km i) = Fin.castLE (Nat.le_trans km mn) i := by grind

example {k m n} (km : k ≤ m) (mn : m ≤ n) :
    Fin.castLE mn ∘ Fin.castLE km = Fin.castLE (Nat.le_trans km mn) := by grind

example (h : n = m) (i : Fin n) : (i.cast h : Nat) = i := by grind

example {k m n} (km : k ≤ m) (mn : m = n) (i : Fin k) :
    Fin.cast mn (i.castLE km) = i.castLE (mn ▸ km) := by grind

example {k m n} (i : Fin k) (h : (i : Nat) < m) (mn : m = n) :
    Fin.cast mn (i.castLT h) = i.castLT (mn ▸ h) := by grind

example [NeZero n] [NeZero m] (h : n = m) : Fin.cast h 0 = 0 := by grind

example {n' : Nat} {h : n + 1 = n' + 1} : (last n).cast h  = last n' := by grind

example (h : n = m) (i : Nat) (hn : i < n) : Fin.cast h ⟨i, hn⟩ = ⟨i, h ▸ hn⟩ := by grind

example (n : Nat) (h : n = n) : Fin.cast h = id := by grind

example {m n : Nat} (h : m = n) {h' : m ≤ n} : castLE h' = Fin.cast h := by grind

example (m : Nat) (i : Fin n) : (castAdd m i : Nat) = i := by grind

example : (castAdd 0 : Fin n → Fin (n + 0)) = Fin.cast rfl := by grind

example {m : Nat} (n : Nat) (i : Fin m) : (castAdd n i : Nat) < m := by grind

example (m : Nat) (i : Nat) (h : i < n) :
    castAdd m ⟨i, h⟩ = ⟨i, Nat.lt_add_right m h⟩ := by grind

example (m : Nat) (i : Fin (n + m)) (hi : i.val < n) :
    castAdd m (castLT i hi) = i := by grind

example (m : Nat) (i : Fin n) :
    castLT (castAdd m i) (castAdd_lt m i) = i := by grind

example {n n' : Nat} (m : Nat) (i : Fin n') (h : n' = n) :
    castAdd m (Fin.cast h i) = Fin.cast (congrArg (. + m) h) (castAdd m i) := by grind

example {n n' m : Nat} (i : Fin n') (h : n' + m = n + m) :
    (i.castAdd m).cast h = (i.cast (Nat.add_right_cancel h)).castAdd m := by grind

example {n m m' : Nat} (i : Fin n) (h : n + m' = n + m) :
    (i.castAdd m').cast h = i.castAdd m := by grind

example {m n p : Nat} (i : Fin m) :
    (i.castAdd n).castAdd p = (i.castAdd (n + p)).cast (Nat.add_assoc ..).symm  := by grind

example {n' : Nat} (i : Fin n) (h : n.succ = n'.succ) :
    i.succ.cast h = (i.cast (Nat.succ.inj h)).succ := by grind

example {n' : Nat} (i : Fin n) (h : n = n') :
    (i.cast h).succ = i.succ.cast (by rw [h]) := by grind

example (i : Fin n) : (i.castSucc : Nat) = i := by grind

example (n i : Nat) (h : i < n) : castSucc ⟨i, h⟩ = ⟨i, Nat.lt.step h⟩ := by grind

example {n' : Nat} {h : n + 1 = n' + 1} {i : Fin n} :
    i.castSucc.cast h = (i.cast (Nat.succ.inj h)).castSucc := by grind

example (i : Fin n) : i.castSucc < i.succ := by grind

example {i : Fin (n + 1)} {j : Fin n} : i ≤ j.castSucc ↔ i < j.succ := by grind

example {n : Nat} {i : Fin n} {j : Fin (n + 1)} :
    i.castSucc < j ↔ i.succ ≤ j := by grind

example (n : Nat) : (last n).succ = last n.succ := by grind

example {n : Nat} {i : Fin n.succ} :
    i.succ = last (n + 1) ↔ i = last n := by grind

example (i : Fin (n + 1)) (h : (i : Nat) < n) :
    (castLT i h).castSucc = i := by grind

example {n : Nat} (a : Fin n) (h : (a : Nat) < n) :
    castLT a.castSucc h = a := by grind

example {a b : Fin n} :
    a.castSucc < b.castSucc ↔ a < b := by grind

example {a b : Fin n} : a.castSucc = b.castSucc ↔ a = b := by grind

example (a : Fin n) : a.castSucc < last n := by grind

example [NeZero n] : castSucc (0 : Fin n) = 0 := by grind

example {n : Nat} : castSucc (1 : Fin (n + 2)) = 1 := by grind

example [NeZero n] {i : Fin n} (h : 0 < i) : 0 < i.castSucc := by grind

example [NeZero n] {a : Fin n} : a.castSucc = 0 ↔ a = 0 := by grind

example [NeZero n] {a : Fin n} : a.castSucc ≠ 0 ↔ a ≠ 0 := by grind

example {a : Fin n} : a.castSucc + 1 = a.succ := by grind

example {a : Fin n} : a.castSucc < a.succ := by grind

example {n : Nat} {i : Fin (n + 1)} : (∃ j, castSucc j = i) ↔ i ≠ last n := by grind

example (m : Nat) (i : Fin n) : (addNat i m : Nat) = i + m := by grind

example (n : Nat) (i : Fin n) : addNat i 0 = i := by grind

example {i : Fin n} : addNat i 1 = i.succ := by grind

example (m : Nat) (i : Fin n) : m ≤ addNat i m := by grind

example (n i : Nat) (hi : i < m) :
    addNat ⟨i, hi⟩ n = ⟨i + n, Nat.add_lt_add_right hi n⟩ := by grind

example {n n' : Nat} (i : Fin n) (h : n + 0 = n') :
    (addNat i 0).cast h = i.cast ((Nat.add_zero _).symm.trans h) := by grind

example {n n' m : Nat} (i : Fin n') (h : n' = n) :
    addNat (i.cast h) m = (addNat i m).cast (congrArg (. + m) h) := by grind

example {n n' m : Nat} (i : Fin n') (h : n' + m = n + m) :
    (addNat i m).cast h = addNat (i.cast (Nat.add_right_cancel h)) m := by grind

example {n m m' : Nat} (i : Fin n) (h : n + m' = n + m) :
    (addNat i m').cast h = addNat i m := by grind

example (n : Nat) {m : Nat} (i : Fin m) : (natAdd n i : Nat) = n + i := by grind

example (n i : Nat) (hi : i < m) :
    natAdd n ⟨i, hi⟩ = ⟨n + i, Nat.add_lt_add_left hi n⟩ := by grind

example (m : Nat) (i : Fin n) : m ≤ natAdd m i := by grind

example {n : Nat} : natAdd 0 = Fin.cast (Nat.zero_add n).symm := by grind

example {n n' : Nat} (m : Nat) (i : Fin n') (h : n' = n) :
    natAdd m (i.cast h) = (natAdd m i).cast (congrArg _ h) := by grind

example {n n' m : Nat} (i : Fin n') (h : m + n' = m + n) :
    (natAdd m i).cast h  = natAdd m (i.cast (Nat.add_left_cancel h)) := by grind

example {n m m' : Nat} (i : Fin n) (h : m' + n = m + n) :
    (natAdd m' i).cast h = natAdd m i := by grind

example (p m : Nat) {n : Nat} (i : Fin n) :
    castAdd p (natAdd m i) = (natAdd m (castAdd p i)).cast (Nat.add_assoc ..).symm := by grind

example (p m : Nat) {n : Nat} (i : Fin n) :
    natAdd m (castAdd p i) = (castAdd p (natAdd m i)).cast (Nat.add_assoc ..) := by grind

example (m n : Nat) {p : Nat} (i : Fin p) :
    natAdd m (natAdd n i) = (natAdd (m + n) i).cast (Nat.add_assoc ..) := by grind

example {n n' : Nat} (i : Fin n) (h : 0 + n = n') :
    (natAdd 0 i).cast h = i.cast ((Nat.zero_add _).symm.trans h) := by grind

example (n : Nat) {m : Nat} (i : Fin m) :
    (natAdd n i).cast (Nat.add_comm ..) = addNat i n := by grind

example {n : Nat} (m : Nat) (i : Fin n) :
    (addNat i m).cast (Nat.add_comm ..) = natAdd m i := by grind

example {m n : Nat} : natAdd n (last m) = last (n + m) := by grind

example (n : Nat) :
    addNat (last n) m = (last (n + m)).cast (by grind) := by grind

example (n : Nat) (i : Fin n) : Fin.natAdd n i = i.addNat n := by grind

example (k : Fin n) (m : Nat) : rev (castAdd m k) = addNat (rev k) m := by grind

example (k : Fin n) (m : Nat) : rev (addNat k m) = castAdd m (rev k) := by grind

example (k : Fin n) : rev (castSucc k) = succ (rev k) := by grind

example (k : Fin n) : rev (succ k) = castSucc (rev k) := by grind

example (j : Fin (n + 1)) (h : j ≠ 0) : (j.pred h : Nat) = j - 1 := by grind

example : ∀ (i : Fin (n + 1)) (h : i ≠ 0), (i.pred h).succ = i := by grind

example (i : Fin n) {h : i.succ ≠ 0} : i.succ.pred h = i := by grind

example {n : Nat} {i : Fin (n + 1)} (hi : i ≠ 0) {j : Fin n} :
    i.pred hi = j ↔ i = j.succ := by grind

example (i : Nat) (h : i < n + 1) :
    Fin.pred ⟨i + 1, Nat.add_lt_add_right h 1⟩ (ne_of_val_ne (Nat.ne_of_gt (mk_succ_pos i h))) =
      ⟨i, h⟩ := by grind

example (i : Nat) (h₁ : i + 1 < n + 1 + 1) (h₂) :
    Fin.pred ⟨i + 1, h₁⟩ h₂ = ⟨i, Nat.lt_of_succ_lt_succ h₁⟩ := by grind

example {n : Nat} (i : Nat) (h : i < n + 1) (w) : Fin.pred ⟨i, h⟩ w =
    ⟨i - 1, Nat.sub_lt_right_of_lt_add (Nat.pos_iff_ne_zero.2 (Fin.val_ne_of_ne w)) h⟩ := by grind

example {n : Nat} {a b : Fin n.succ} {ha : a ≠ 0} {hb : b ≠ 0} :
    a.pred ha ≤ b.pred hb ↔ a ≤ b := by grind

example {n : Nat} {a b : Fin n.succ} {ha : a ≠ 0} {hb : b ≠ 0} :
    a.pred ha < b.pred hb ↔ a < b := by grind

example :
    ∀ {a b : Fin (n + 1)} {ha : a ≠ 0} {hb : b ≠ 0}, a.pred ha = b.pred hb ↔ a = b := by grind

example {n : Nat} :
    Fin.pred (1 : Fin (n + 2)) (Ne.symm (Fin.ne_of_lt one_pos)) = 0 := by grind

example (i : Fin (n + 2)) (h : (i : Nat) < n + 1) :
    pred (i + 1) (Fin.ne_of_gt (add_one_pos _ (lt_def.2 h))) = castLT i h := by grind

example (i : Fin (n + m)) (h : m ≤ i) : (i.subNat m h : Nat) = i - m := by grind

example {i : Nat} (h₁ : i < n + m) (h₂ : m ≤ i) :
    subNat m ⟨i, h₁⟩ h₂ = ⟨i - m, Nat.sub_lt_right_of_lt_add h₂ h₁⟩ := by grind

example (i : Fin n) (h : 0 ≤ (i : Nat)): Fin.subNat 0 i h = i := by grind

example (i : Fin (n + 1)) (h : 1 ≤ (i : Nat)) : (subNat 1 i h).succ = i := by grind

example (i : Fin n) :
    pred (castSucc i.succ) (Fin.ne_of_gt (castSucc_pos i.succ_pos)) = castSucc i := by grind

example {i : Fin (n + m)} (h : m ≤ i) : addNat (subNat m i h) m = i := by grind

example (i : Fin n) (m : Nat) (h : m ≤ addNat i m := le_coe_addNat m i) :
    subNat m (addNat i m) h = i := by grind

example {i : Fin (n + m)} (h : n ≤ i) :
    natAdd n (subNat n (i.cast (Nat.add_comm ..)) h) = i := by grind

/-! ### Recursion and induction principles -/

example {motive : ∀ n, Fin n → Sort _} {zero succ} (n) :
    @Fin.succRecOn (n + 1) 0 motive zero succ = zero n := by grind

example {motive : ∀ n, Fin n → Sort _} {zero succ} {n} (i : Fin n) :
    @Fin.succRecOn (n + 1) i.succ motive zero succ = succ n i (Fin.succRecOn i zero succ) := by grind

example {motive : Fin (n + 1) → Sort _} (zero : motive 0)
    (hs : ∀ i : Fin n, motive (castSucc i) → motive i.succ) :
    (induction zero hs : ∀ i : Fin (n + 1), motive i) 0 = zero := by grind

example {motive : Fin (n + 1) → Sort _} (zero : motive 0)
    (succ : ∀ i : Fin n, motive (castSucc i) → motive i.succ) (i : Fin n) :
    induction (motive := motive) zero succ i.succ = succ i (induction zero succ (castSucc i)) := by grind

example {n} {motive : Fin (n + 1) → Sort _} {zero succ} :
    @Fin.cases n motive zero succ 0 = zero := by grind

example {n} {motive : Fin (n + 1) → Sort _} {zero succ} (i : Fin n) :
    @Fin.cases n motive zero succ i.succ = succ i := by grind

example {n} {motive : Fin (n + 1) → Sort _} {zero succ}
    {i : Nat} (h : i + 1 < n + 1) :
    @Fin.cases n motive zero succ ⟨i.succ, h⟩ = succ ⟨i, Nat.lt_of_succ_lt_succ h⟩ := by grind

example {P : Fin (n + 1) → Prop} : (∀ i, P i) ↔ P 0 ∧ ∀ i : Fin n, P i.succ := by grind

example {P : Fin (n + 1) → Prop} : (∃ i, P i) ↔ P 0 ∨ ∃ i : Fin n, P i.succ := by grind

example {p : Fin 1 → Prop} : (∀ i, p i) ↔ p 0 := by grind

example {p : Fin 1 → Prop} : (∃ i, p i) ↔ p 0 := by grind

example {p : Fin 2 → Prop} : (∀ i, p i) ↔ p 0 ∧ p 1 := by grind

example {p : Fin 2 → Prop} : (∃ i, p i) ↔ p 0 ∨ p 1 := by grind

example {n : Nat} {motive : Fin (n + 1) → Sort _} {zero succ} :
    (reverseInduction zero succ (Fin.last n) : motive (Fin.last n)) = zero := by grind

example {n : Nat} {motive : Fin (n + 1) → Sort _} {zero succ}
    (i : Fin n) : reverseInduction (motive := motive) zero succ (castSucc i) =
      succ i (reverseInduction zero succ i.succ) := by grind

example {n : Nat} {motive : Fin (n + 1) → Sort _} {last cast} :
    (Fin.lastCases last cast (Fin.last n) : motive (Fin.last n)) = last := by grind

example {n : Nat} {motive : Fin (n + 1) → Sort _} {last cast}
    (i : Fin n) : (Fin.lastCases last cast (Fin.castSucc i) : motive (Fin.castSucc i)) = cast i := by grind

example {m n : Nat} {motive : Fin (m + n) → Sort _} {left right} (i : Fin m) :
    addCases (motive := motive) left right (Fin.castAdd n i) = left i := by grind

example {m n : Nat} {motive : Fin (m + n) → Sort _} {left right} (i : Fin n) :
    addCases (motive := motive) left right (natAdd m i) = right i := by grind

example [NeZero n] {a : Fin n} : a.val = 0 ↔ a = 0 := by grind

example [NeZero n] {a : Fin n} : a.val ≠ 0 ↔ a ≠ 0 := by grind

example [NeZero n] (x : Nat) (y : Fin n) :
    Fin.ofNat n x + y = Fin.ofNat n (x + y.val) := by grind

example [NeZero n] (x : Fin n) (y : Nat) :
    x + Fin.ofNat n y = Fin.ofNat n (x.val + y) := by grind


example (a b : Fin n) : ((a - b : Fin n) : Nat) = ((n - b) + a) % n := by grind

example [NeZero n] (x : Nat) (y : Fin n) :
    Fin.ofNat n x - y = Fin.ofNat n ((n - y.val) + x) := by grind

example [NeZero n] (x : Fin n) (y : Nat) :
    x - Fin.ofNat n y = Fin.ofNat n ((n - y % n) + x.val) := by grind

example {x n} (h₁ : n ≤ x) (h₂ : x < 2 * n) :
    x % n = x - n := by grind

example {a b : Fin n} : (↑(a - b) : Nat) = a - b ↔ b ≤ a := by grind

example {a b : Fin n} : b ≤ a → (a - b).val = a.val - b.val := by grind

example {a b : Fin n} : (↑(a - b) : Nat) = n + a - b ↔ a < b := by grind

/-! ### neg -/

example {n : Nat} [NeZero n] (x : Fin n) :
    (-x).val = if x = 0 then 0 else n - x.val := by grind

example {n : Nat} (x y : Fin n) : x - y = x + -y := by grind

/-! ### mul -/

example [NeZero n] (x : Nat) (y : Fin n) :
    Fin.ofNat n x * y = Fin.ofNat n (x * y.val) := by grind

example [NeZero n] (x : Fin n) (y : Nat) :
    x * Fin.ofNat n y = Fin.ofNat n (x.val * y) := by grind
