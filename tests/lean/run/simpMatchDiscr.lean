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
`simp` does not try to apply congruence to parameters with forward dependencies (e.g. `n` in `map`).
-/

theorem ex1 (a b : Nat) (as : Vec Nat n) : foo (Vec.cons a as) (Vec.cons b as) id 0 = a + b := by
  simp [foo]

/-!
`simp` can handle overapplications of match applications.
-/

def bla (b : Bool) (f g : α → β) (a : α) : β :=
  (match b with
   | true => f | false => g) a

theorem ex2 (h : b = false) : bla b (fun x => x + 1) id 10 = 10 := by
  simp [bla, h]

/-!
`simp` works with equations on the match discriminants.
-/

def test1 (n : Nat) : Nat :=
  match _ : n with
  | 0 => 32
  | _ + 1 => 0

example (h : a = 3) : test1 a = 0 := by
  simp [test1, h]

/-!
`simp` works with proof parameters with backward dependencies (even if they have equations
associated with them).
-/

def test2 (n : Nat) (h : n ≠ 0) : Nat :=
  match _ : n, _ : h with
  | k + 1, _ => k

example (h : a = 3) : test2 a h' = 2 := by
  simp [test2, h]

/-!
Congruence also works in `dsimp`.
-/

example : test2 (id 3) h = 2 := by
  unfold test2
  dsimp only [id_eq]

structure Test (n : Nat) where
  value : Nat

/-!
`simp` doesn't apply congruence if the motive depends on the discriminant.
-/

def abc (x : Nat) : Test x :=
  match x with
  | 0 => Test.mk 27
  | 1 => Test.mk 5
  | _ + 2 => Test.mk 3

/--
error: unsolved goals
a : Nat
h : a = 3
⊢ (match a with
      | 0 => { value := 27 }
      | 1 => { value := 5 }
      | n.succ.succ => { value := 3 }).value =
    3
-/
#guard_msgs in
example (h : a = 3) : (abc a).value = 3 := by
  simp [abc, h]

/-!
Similar to previous test but eta-reduce motive.
-/

def abc' (x : Nat) : Test x :=
  abc.match_1 Test x (fun _ => Test.mk 27) (fun _ => Test.mk 5) (fun _ => Test.mk 3)

/--
error: unsolved goals
a : Nat
h : a = 3
⊢ (match a with
      | 0 => { value := 27 }
      | 1 => { value := 5 }
      | x.succ.succ => { value := 3 }).value =
    3
-/
#guard_msgs in
example (h : a = 3) : (abc' a).value = 3 := by
  simp [abc', h]

/-!
`simp` *does* apply congruence if the motive depends on one the discriminant but not another.
-/

def abc2 (x y : Nat) : Test x :=
  match x, y with
  | _, 0 => Test.mk 27
  | _, 1 => Test.mk 5
  | _, _ + 2 => Test.mk 3

example (_h : a = 3) (h' : b = 3) : (abc2 a b).value = 3 := by
  simp only [abc2]
  fail_if_success simp only [_h]
  simp only [h']

/-!
`simp` works when a proof depends on another proof.
-/

structure WithProof {p : Prop} (h : p) : Prop where

def xyz (x : Nat) (h : x ≠ 0) (w : WithProof h) : Nat :=
  match x, h, w with
  | 3, _, _ => 8
  | _, _, _ => 2

theorem t (h : x = 3) : xyz x h' w = 8 := by
  simp [xyz, h]

#print t

#print xyz.match_1.discr_congr
