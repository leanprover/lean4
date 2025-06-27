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

/--
info: Vec.map.match_1.discr_congr.{u_1, u_2} {α : Type u_1} (motive : (n : Nat) → Vec α n → Sort u_2) (n✝ : Nat)
  (v✝ : Vec α n✝) (h_1 : Unit → motive 0 Vec.nil)
  (h_2 : (a : α) → (n : Nat) → (as : Vec α n) → motive (n + 1) (Vec.cons a as)) (v✝¹ : Vec α n✝) (heq : v✝ = v✝¹) :
  (match n✝, v✝ with
    | .(0), Vec.nil => h_1 ()
    | .(n + 1), Vec.cons a as => h_2 a n as) ≍
    match n✝, v✝¹ with
    | .(0), Vec.nil => h_1 ()
    | .(n + 1), Vec.cons a as => h_2 a n as
-/
#guard_msgs in
#check Vec.map.match_1.discr_congr

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

/--
info: test1.match_1.discr_congr.{u_1} (motive : Nat → Sort u_1) (n✝ : Nat) (h_1 : n✝ = 0 → motive 0)
  (h_2 : (n : Nat) → n✝ = n.succ → motive n.succ) (n✝¹ : Nat) (heq : n✝ = n✝¹) :
  (match h : n✝ with
    | 0 => h_1 h
    | n.succ => h_2 n h) ≍
    match h : n✝¹ with
    | 0 => h_1 ⋯
    | n.succ => h_2 n ⋯
-/
#guard_msgs in
#check test1.match_1.discr_congr

example (h : a = 3) : test1 a = 0 := by
  simp [test1, h]

/-!
`simp` works with proof parameters with backward dependencies (even if they have equations
associated with them).
-/

def test2 (n : Nat) (h : n ≠ 0) : Nat :=
  match _ : n, _ : h with
  | k + 1, _ => k

/--
info: test2.match_1.discr_congr.{u_1} (motive : (n : Nat) → n ≠ 0 → Sort u_1) (n✝ : Nat) (h✝ : n✝ ≠ 0)
  (h_1 : (k : Nat) → (x : k + 1 ≠ 0) → n✝ = k.succ → h✝ ≍ x → motive k.succ x) (n✝¹ : Nat) (heq : n✝ = n✝¹) :
  (match h : n✝, h : h✝ with
    | k.succ, x => h_1 k x h h) ≍
    match h : n✝¹, h : ⋯ with
    | k.succ, x => h_1 k x ⋯ ⋯
-/
#guard_msgs in
#check test2.match_1.discr_congr

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
info: abc.match_1.discr_congr.{u_1} (motive : Nat → Sort u_1) (x✝ : Nat) (h_1 : Unit → motive 0) (h_2 : Unit → motive 1)
  (h_3 : (n : Nat) → motive n.succ.succ) (x✝¹ : Nat) (heq : x✝ = x✝¹) :
  (match x✝ with
    | 0 => h_1 ()
    | 1 => h_2 ()
    | n.succ.succ => h_3 n) ≍
    match x✝¹ with
    | 0 => h_1 ()
    | 1 => h_2 ()
    | n.succ.succ => h_3 n
-/
#guard_msgs in
#check abc.match_1.discr_congr

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

/--
info: abc2.match_1.discr_congr.{u_1} (motive : Nat → Nat → Sort u_1) (x✝ y✝ : Nat) (h_1 : (x : Nat) → motive x 0)
  (h_2 : (x : Nat) → motive x 1) (h_3 : (x n : Nat) → motive x n.succ.succ) (x✝¹ : Nat) (heq : x✝ = x✝¹) (y✝¹ : Nat) :
  y✝ = y✝¹ →
    (match x✝, y✝ with
      | x, 0 => h_1 x
      | x, 1 => h_2 x
      | x, n.succ.succ => h_3 x n) ≍
      match x✝¹, y✝¹ with
      | x, 0 => h_1 x
      | x, 1 => h_2 x
      | x, n.succ.succ => h_3 x n
-/
#guard_msgs in
#check abc2.match_1.discr_congr

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

/--
info: xyz.match_1.discr_congr.{u_1} (motive : (x : Nat) → (h : x ≠ 0) → WithProof h → Sort u_1) (x✝ : Nat) (h✝ : x✝ ≠ 0)
  (w✝ : WithProof h✝) (h_1 : (x : 3 ≠ 0) → (x_1 : WithProof x) → motive 3 x x_1)
  (h_2 : (x : Nat) → (x_1 : x ≠ 0) → (x_2 : WithProof x_1) → motive x x_1 x_2) (x✝¹ : Nat) (heq : x✝ = x✝¹) :
  (match x✝, h✝, w✝ with
    | 3, x, x_1 => h_1 x x_1
    | x, x_1, x_2 => h_2 x x_1 x_2) ≍
    match x✝¹, ⋯, ⋯ with
    | 3, x, x_1 => h_1 x x_1
    | x, x_1, x_2 => h_2 x x_1 x_2
-/
#guard_msgs in
#check xyz.match_1.discr_congr

theorem t (h : x = 3) : xyz x h' w = 8 := by
  simp +singlePass only [xyz, h]

/-!
Congruence principle gets generated correctly even if a discriminant is a forall.
-/

def a (x : Nat) (h : ∀ a : Nat, x = a → a = x) : Nat :=
  match x, h with
  | 0, _ => 3
  | _ + 1, _ => 9

/--
info: a.match_1.discr_congr.{u_1} (motive : (x : Nat) → (∀ (a : Nat), x = a → a = x) → Sort u_1) (x✝ : Nat)
  (h✝ : ∀ (a : Nat), x✝ = a → a = x✝) (h_1 : (x : ∀ (a : Nat), 0 = a → a = 0) → motive 0 x)
  (h_2 : (n : Nat) → (x : ∀ (a : Nat), n + 1 = a → a = n + 1) → motive n.succ x) (x✝¹ : Nat) (heq : x✝ = x✝¹) :
  (match x✝, h✝ with
    | 0, x => h_1 x
    | n.succ, x => h_2 n x) ≍
    match x✝¹, ⋯ with
    | 0, x => h_1 x
    | n.succ, x => h_2 n x
-/
#guard_msgs in
#check a.match_1.discr_congr
