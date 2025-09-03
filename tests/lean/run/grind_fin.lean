open Fin

example (n : Nat) [NeZero n] : Fin.ofNat n 0 = 0 := by grind

example (a b : Fin n) : (a % b).val = a.val % b.val := by grind
example (a b : Fin n) : (a * b).val = (a.val * b.val) % n := by grind
example (a b : Fin n) : (a - b).val = ((n - b.val) + a.val) % n := by grind

example (a : Fin n) : a < n := by grind

example {a b : Fin n} : a.1 ≠ b.1 ↔ a ≠ b := by grind

example {n a : Nat} {ha : a < n} [NeZero n] :
    (⟨a, ha⟩ : Fin n) = 0 ↔ a = 0 := by grind

example {n : Nat} [NeZero n] : Fin.ofNat n n = 0 := by grind

example [NeZero n] (x : Fin n) : (Fin.ofNat n x.val) = x := by grind

example (a : Fin 1) : a.val = 0 := by grind
example (a : Fin 2) : a.val = 0 ∨ a.val = 1 := by grind

example (a : Fin 37) : a.val < 47 := by grind
example (a : Fin (n + 37)) : a.val < n + 47 := by grind
example (a : Fin (2 * n + 1)) : a.val < 2 * (n + 1) := by grind
example (a : Fin (2 * n + 1)) : a.val + (-a).val = 2 * n + 1 := by grind

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

example [NeZero n] {a : Fin n} : 0 < a ↔ a ≠ 0 := by grind

example {x y : Fin n} : x = y ↔ x ≤ y ∧ y ≤ x := by grind

example (i : Fin n) : rev (rev i) = i := by grind

example {i j : Fin n} : rev i ≤ rev j ↔ j ≤ i := by grind

example {i j : Fin n} : rev i = rev j ↔ i = j := by grind

example (n : Nat) : (last n).1 = n := by grind

example : (Fin.last 0 : Fin 1) = 0 := by grind

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

example (h : n ≤ m) (i : Fin n) : (castLE h i : Nat) = i := by grind

example (i n m : Nat) (hn : i < n) (h : n ≤ m) :
    castLE h ⟨i, hn⟩ = ⟨i, Nat.lt_of_lt_of_le hn h⟩ := by grind

example {n m : Nat} (h : n.succ ≤ m.succ) : castLE h 0 = 0 := by grind

example {m n : Nat} (h : m + 1 ≤ n + 1) (i : Fin m) :
    castLE h i.succ = (castLE (Nat.succ_le_succ_iff.mp h) i).succ := by grind

example {k m n} (km : k ≤ m) (mn : m ≤ n) (i : Fin k) :
    Fin.castLE mn (Fin.castLE km i) = Fin.castLE (Nat.le_trans km mn) i := by grind

example {k m n} (km : k ≤ m) (mn : m ≤ n) :
    Fin.castLE mn ∘ Fin.castLE km = Fin.castLE (Nat.le_trans km mn) := by grind

example (h : n = m) (i : Fin n) : (i.cast h : Nat) = i := rfl

example {k m n} (km : k ≤ m) (mn : m = n) (i : Fin k) :
    Fin.cast mn (i.castLE km) = i.castLE (mn ▸ km) := by grind

example {k m n} (i : Fin k) (h : (i : Nat) < m) (mn : m = n) :
    Fin.cast mn (i.castLT h) = i.castLT (mn ▸ h) := by grind

example [NeZero n] [NeZero m] (h : n = m) : Fin.cast h 0 = 0 := by grind

example {n' : Nat} {h : n + 1 = n' + 1} : (last n).cast h  = last n' := by grind

example (h : n = m) (i : Nat) (hn : i < n) : Fin.cast h ⟨i, hn⟩ = ⟨i, h ▸ hn⟩ := by grind

example (n : Nat) (h : n = n) : Fin.cast h = id := by grind

example {k : Nat} (h : n = m) (h' : m = k) {i : Fin n} :
    (i.cast h).cast h' = i.cast (Eq.trans h h') := by grind

example {m n : Nat} (h : m = n) {h' : m ≤ n} : castLE h' = Fin.cast h := by grind rfl

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
    i.succ = last (n + 1) ↔ i = last n := by by grind

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

example (n : Nat) (j : Fin n) :
    j.succ.castSucc = (j.castSucc).succ := by grind

example {a : Fin n} : a.castSucc + 1 = a.succ := by grind

example {a : Fin n} : a.castSucc < a.succ := by grind

example {n : Nat} {i : Fin (n + 1)} : (∃ j, castSucc j = i) ↔ i ≠ last n := by grind

example {n : Nat} (i : Fin n) : i.castSucc.succ = i.succ.castSucc := by grind
