def find42 : Nat → Bool
  | 42 => true
  | n => find42 (n + 1)
partial_fixpoint

/--
info: find42.eq_def (x✝ : Nat) :
  find42 x✝ =
    match x✝ with
    | 42 => true
    | n => find42 (n + 1)
-/
#guard_msgs in
#check find42.eq_def

/--
info: equations:
theorem find42.eq_1 : find42 42 = true
theorem find42.eq_2 : ∀ (x : Nat), (x = 42 → False) → find42 x = find42 (x + 1)
-/
#guard_msgs in
#print equations find42

mutual
def find99 : Nat → Bool
  | 99 => true
  | n => find23 (n + 1)
partial_fixpoint
def find23 : Nat → Bool
  | 23 => true
  | n => find99 (n + 1)
partial_fixpoint
end

/--
info: find99.eq_def (x✝ : Nat) :
  find99 x✝ =
    match x✝ with
    | 99 => true
    | n => find23 (n + 1)
-/
#guard_msgs in
#check find99.eq_def

/--
info: find23.eq_def (x✝ : Nat) :
  find23 x✝ =
    match x✝ with
    | 23 => true
    | n => find99 (n + 1)
-/
#guard_msgs in
#check find23.eq_def

/--
info: equations:
theorem find99.eq_1 : find99 99 = true
theorem find99.eq_2 : ∀ (x : Nat), (x = 99 → False) → find99 x = find23 (x + 1)
-/
#guard_msgs in
#print equations find99

/--
info: equations:
theorem find23.eq_1 : find23 23 = true
theorem find23.eq_2 : ∀ (x : Nat), (x = 23 → False) → find23 x = find99 (x + 1)
-/
#guard_msgs in
#print equations find23


mutual
def g (i j : Nat) : Nat :=
  if i < 5 then 0 else
  match j with
  | Nat.zero => 1
  | Nat.succ j => h i j
partial_fixpoint

def h (i j : Nat) : Nat :=
  match j with
  | 0 => g i 0
  | Nat.succ j => g i j
partial_fixpoint
end

/--
info: equations:
theorem g.eq_1 : ∀ (i : Nat), g i Nat.zero = if i < 5 then 0 else 1
theorem g.eq_2 : ∀ (i j_2 : Nat), g i j_2.succ = if i < 5 then 0 else h i j_2
-/
#guard_msgs in
#print equations g

/--
info: equations:
theorem h.eq_1 : ∀ (i : Nat), h i 0 = g i 0
theorem h.eq_2 : ∀ (i j_2 : Nat), h i j_2.succ = g i j_2
-/
#guard_msgs in
#print equations h
