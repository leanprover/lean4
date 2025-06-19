/-!
# `simp` on match discriminants

Tests that `simp` can apply congruence to match discrimants.
-/

inductive Vec (α : Type u) : Nat → Type u
  | nil  : Vec α 0
  | cons : α → {n : Nat} → Vec α n → Vec α (n+1)

def Vec.repeat (a : α) (n : Nat) : Vec α n :=
  match n with
  | 0   => nil
  | n+1 => cons a («repeat» a n)

instance [Inhabited α] : Inhabited (Vec α n) where
  default := Vec.repeat default n

def Vec.map (v : Vec α n) (f : α → β) : Vec β n :=
  match n, v with
  | _, nil       => nil
  | _, cons a as => cons (f a) (map as f)

def Vec.reverse (v : Vec α n) : Vec α n :=
  let rec loop {n m : Nat} : Vec α n → Vec α m → Vec α (n + m)
    | nil,       w => Nat.zero_add .. ▸ w
    | cons a as, w => Nat.add_assoc .. ▸ loop as (Nat.add_comm .. ▸ cons a w)
  loop v nil

@[simp] theorem map_id (v : Vec α n) : v.map id = v := by
  induction v with
  | nil => rfl
  | cons a as ih => simp [Vec.map, ih]

def foo [Add α] (v w : Vec α n) (f : α → α) (a : α) : α :=
  match n, v.map f, w.map f with
  | _, Vec.nil,       Vec.nil       => a
  | _, Vec.cons a .., Vec.cons b .. => a + b

/-!
Test that `simp` does not try to apply congruence to parameters with forward dependencies
(e.g. `n` in `map`).
-/

theorem ex1 (a b : Nat) (as : Vec Nat n) : foo (Vec.cons a as) (Vec.cons b as) id 0 = a + b := by
  simp [foo]

/-!
Tests that `simp` can handle overapplications of match applications.
-/

def bla (b : Bool) (f g : α → β) (a : α) : β :=
  (match b with
   | true => f | false => g) a

theorem ex2 (h : b = false) : bla b (fun x => x + 1) id 10 = 10 := by
  simp [bla, h]

/-!
Tests that `simp` works with equations on the match discriminants.
-/

def test1 (n : Nat) : Nat :=
  match _ : n with
  | 0 => 32
  | _ + 1 => 0

example (h : a = 3) : test1 a = 0 := by
  simp [test1, h]

/-!
Tests that `simp` works with proof parameters with backward dependencies (even if they have
equations associated with them).
-/

def test2 (n : Nat) (h : n ≠ 0) : Nat :=
  match _ : n, _ : h with
  | k + 1, _ => k

example (h : a = 3) : test2 a h' = 2 := by
  simp [test2, h]

/-!
Tests that congruence also works in `dsimp`.
-/

example : test2 (id 3) h = 2 := by
  unfold test2
  dsimp only [id_eq]
