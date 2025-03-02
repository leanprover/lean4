def loop (x : Nat) : Unit := loop (x + 1)
partial_fixpoint

/--
info: loop.fixpoint_induct (motive : (Nat → Unit) → Prop) (adm : Lean.Order.admissible motive)
  (h : ∀ (loop : Nat → Unit), motive loop → motive fun x => loop (x + 1)) : motive loop
-/
#guard_msgs in #check loop.fixpoint_induct


/-- error: unknown constant 'loop.partial_correctness' -/
#guard_msgs in #check loop.partial_correctness


def find (P : Nat → Bool) (x : Nat) : Option Nat :=
  if P x then
    some x
  else
    find P (x +1)
partial_fixpoint

/--
info: find.fixpoint_induct (P : Nat → Bool) (motive : (Nat → Option Nat) → Prop) (adm : Lean.Order.admissible motive)
  (h : ∀ (find : Nat → Option Nat), motive find → motive fun x => if P x = true then some x else find (x + 1)) :
  motive (find P)
-/
#guard_msgs in #check find.fixpoint_induct

/--
info: find.partial_correctness (P : Nat → Bool) (motive : Nat → Nat → Prop)
  (h :
    ∀ (find : Nat → Option Nat),
      (∀ (x r : Nat), find x = some r → motive x r) →
        ∀ (x r : Nat), (if P x = true then some x else find (x + 1)) = some r → motive x r)
  (x r✝ : Nat) : find P x = some r✝ → motive x r✝
-/
#guard_msgs in #check find.partial_correctness

def fib (n : Nat) := go 0 0 1
where
  go i fip fi :=
    if i = n then
      fi
    else
      go (i + 1) fi (fi + fip)
  partial_fixpoint

/--
info: fib.go.fixpoint_induct (n : Nat) (motive : (Nat → Nat → Nat → Nat) → Prop) (adm : Lean.Order.admissible motive)
  (h :
    ∀ (go : Nat → Nat → Nat → Nat), motive go → motive fun i fip fi => if i = n then fi else go (i + 1) fi (fi + fip)) :
  motive (fib.go n)
-/
#guard_msgs in #check fib.go.fixpoint_induct


local instance (b : Bool) [Nonempty α] [Nonempty β] : Nonempty (cond b α β) := by
  cases b <;> assumption
local instance (b : Bool) [Nonempty α] [Nonempty β] : Nonempty (if b then α else β) := by
  split <;> assumption

mutual
def dependent2''a (m n : Nat) (b : Bool) : if b then Nat else Bool :=
  if _ : b then dependent2''a m (n + 1) b else dependent2''b m m (n + m) b
partial_fixpoint
def dependent2''b (m k n : Nat) (b : Bool) : if b then Nat else Bool :=
  if b then dependent2''b m k n b else dependent2''c m (.last _) (n + m) b
partial_fixpoint
def dependent2''c (m : Nat) (i : Fin (m+1)) (n : Nat) (b : Bool) : if b then Nat else Bool :=
  if b then dependent2''c m i n b else dependent2''a m i b
partial_fixpoint
end

/--
info: dependent2''a.fixpoint_induct (m : Nat) (b : Bool) (motive_1 : (Nat → if b = true then Nat else Bool) → Prop)
  (motive_2 : (Nat → Nat → if b = true then Nat else Bool) → Prop)
  (motive_3 : (Fin (m + 1) → Nat → if b = true then Nat else Bool) → Prop) (adm_1 : Lean.Order.admissible motive_1)
  (adm_2 : Lean.Order.admissible motive_2) (adm_3 : Lean.Order.admissible motive_3)
  (h_1 :
    ∀ (dependent2''a : Nat → if b = true then Nat else Bool)
      (dependent2''b : Nat → Nat → if b = true then Nat else Bool),
      motive_1 dependent2''a →
        motive_2 dependent2''b →
          motive_1 fun n => if x : b = true then dependent2''a (n + 1) else dependent2''b m (n + m))
  (h_2 :
    ∀ (dependent2''b : Nat → Nat → if b = true then Nat else Bool)
      (dependent2''c : Fin (m + 1) → Nat → if b = true then Nat else Bool),
      motive_2 dependent2''b →
        motive_3 dependent2''c →
          motive_2 fun k n => if b = true then dependent2''b k n else dependent2''c (Fin.last m) (n + m))
  (h_3 :
    ∀ (dependent2''a : Nat → if b = true then Nat else Bool)
      (dependent2''c : Fin (m + 1) → Nat → if b = true then Nat else Bool),
      motive_1 dependent2''a →
        motive_3 dependent2''c → motive_3 fun i n => if b = true then dependent2''c i n else dependent2''a ↑i) :
  (motive_1 fun n => dependent2''a m n b) ∧
    (motive_2 fun k n => dependent2''b m k n b) ∧ motive_3 fun i n => dependent2''c m i n b
-/
#guard_msgs in #check dependent2''a.fixpoint_induct

/-- error: unknown constant 'dependent2''b.fixpoint_induct' -/
#guard_msgs in #check dependent2''b.fixpoint_induct


mutual
def dependent3''a (m n : Nat) (b : Bool) : Option (if b then Nat else Bool) :=
  if _ : b then dependent3''a m (n + 1) b else dependent3''b m m (n + m) b
partial_fixpoint
def dependent3''b (m k n : Nat) (b : Bool) : Option (if b then Nat else Bool) :=
  if b then dependent3''b m k n b else dependent3''c m (.last _) (n + m) b
partial_fixpoint
def dependent3''c (m : Nat) (i : Fin (m+1)) (n : Nat) (b : Bool) : Option (if b then Nat else Bool) :=
  if b then dependent3''c m i n b else dependent3''a m i b
partial_fixpoint
end

/--
info: dependent3''a.partial_correctness (m : Nat) (b : Bool) (motive_1 : Nat → (if b = true then Nat else Bool) → Prop)
  (motive_2 : Nat → Nat → (if b = true then Nat else Bool) → Prop)
  (motive_3 : Fin (m + 1) → Nat → (if b = true then Nat else Bool) → Prop)
  (h_1 :
    ∀ (dependent3''a : Nat → Option (if b = true then Nat else Bool))
      (dependent3''b : Nat → Nat → Option (if b = true then Nat else Bool)),
      (∀ (n : Nat) (r : if b = true then Nat else Bool), dependent3''a n = some r → motive_1 n r) →
        (∀ (k n : Nat) (r : if b = true then Nat else Bool), dependent3''b k n = some r → motive_2 k n r) →
          ∀ (n : Nat) (r : if b = true then Nat else Bool),
            (if x : b = true then dependent3''a (n + 1) else dependent3''b m (n + m)) = some r → motive_1 n r)
  (h_2 :
    ∀ (dependent3''b : Nat → Nat → Option (if b = true then Nat else Bool))
      (dependent3''c : Fin (m + 1) → Nat → Option (if b = true then Nat else Bool)),
      (∀ (k n : Nat) (r : if b = true then Nat else Bool), dependent3''b k n = some r → motive_2 k n r) →
        (∀ (i : Fin (m + 1)) (n : Nat) (r : if b = true then Nat else Bool),
            dependent3''c i n = some r → motive_3 i n r) →
          ∀ (k n : Nat) (r : if b = true then Nat else Bool),
            (if b = true then dependent3''b k n else dependent3''c (Fin.last m) (n + m)) = some r → motive_2 k n r)
  (h_3 :
    ∀ (dependent3''a : Nat → Option (if b = true then Nat else Bool))
      (dependent3''c : Fin (m + 1) → Nat → Option (if b = true then Nat else Bool)),
      (∀ (n : Nat) (r : if b = true then Nat else Bool), dependent3''a n = some r → motive_1 n r) →
        (∀ (i : Fin (m + 1)) (n : Nat) (r : if b = true then Nat else Bool),
            dependent3''c i n = some r → motive_3 i n r) →
          ∀ (i : Fin (m + 1)) (n : Nat) (r : if b = true then Nat else Bool),
            (if b = true then dependent3''c i n else dependent3''a ↑i) = some r → motive_3 i n r) :
  (∀ (n : Nat) (r : if b = true then Nat else Bool), dependent3''a m n b = some r → motive_1 n r) ∧
    (∀ (k n : Nat) (r : if b = true then Nat else Bool), dependent3''b m k n b = some r → motive_2 k n r) ∧
      ∀ (i : Fin (m + 1)) (n : Nat) (r : if b = true then Nat else Bool),
        dependent3''c m i n b = some r → motive_3 i n r
-/
#guard_msgs in #check dependent3''a.partial_correctness

-- The following example appears in the manual; having it here alerts us early of breakage

def List.findIndex (xs : List α) (p : α → Bool) : Option Nat := match xs with
  | [] => none
  | x::ys =>
    if p x then
      some 0
    else
      (· + 1) <$> List.findIndex ys p
partial_fixpoint

/--
info: List.findIndex.partial_correctness.{u_1} {α : Type u_1} (p : α → Bool) (motive : List α → Nat → Prop)
  (h :
    ∀ (findIndex : List α → Option Nat),
      (∀ (xs : List α) (r : Nat), findIndex xs = some r → motive xs r) →
        ∀ (xs : List α) (r : Nat),
          (match xs with
              | [] => none
              | x :: ys => if p x = true then some 0 else (fun x => x + 1) <$> findIndex ys) =
              some r →
            motive xs r)
  (xs : List α) (r✝ : Nat) : xs.findIndex p = some r✝ → motive xs r✝
-/
#guard_msgs in
#check List.findIndex.partial_correctness

theorem List.findIndex_implies_pred (xs : List α) (p : α → Bool) :
    xs.findIndex p = some i → xs[i]?.any p := by
  apply List.findIndex.partial_correctness (motive := fun xs i => xs[i]?.any p)
  intro findIndex ih xs r hsome
  split at hsome
  next => contradiction
  next x ys =>
    split at hsome
    next =>
      have : r = 0 := by simp_all
      simp_all
    next =>
      simp only [Option.map_eq_map, Option.map_eq_some'] at hsome
      obtain ⟨r', hr, rfl⟩ := hsome
      specialize ih _ _ hr
      simpa
