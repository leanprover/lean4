inductive Vec (α : Type u) : Nat → Type u
  | nil  : Vec α 0
  | cons : α → {n : Nat} → Vec α n → Vec α (n+1)

def Vec.repeat (a : α) (n : Nat) : Vec α n :=
  match n with
  | 0   => nil
  | n+1 => cons a (repeat a n)

instance [Inhabited α] : Inhabited (Vec α n) where
  default := Vec.repeat arbitrary n

def Vec.map (v : Vec α n) (f : α → β) : Vec β n :=
  match n, v with
  | _, nil       => nil
  | _, cons a as => cons (f a) (map as f)

def Vec.reverse (v : Vec α n) : Vec α n :=
  let rec loop : {n m : Nat} → Vec α n → Vec α m → Vec α (n + m)
    | _, _, nil,       w => Nat.zero_add .. ▸ w
    | _, _, cons a as, w => Nat.add_assoc .. ▸ loop as (Nat.add_comm .. ▸ cons a w)
  loop v nil

@[simp] theorem map_id (v : Vec α n) : v.map id = v := by
  induction v with
  | nil => rfl
  | cons a as ih => simp [Vec.map, ih]

def foo [Add α] (v w : Vec α n) (f : α → α) (a : α) : α :=
  match n, v.map f, w.map f with
  | _, Vec.nil,       Vec.nil       => a
  | _, Vec.cons a .., Vec.cons b .. => a + b

theorem ex1 (a b : Nat) (as : Vec Nat n) : foo (Vec.cons a as) (Vec.cons b as) id 0 = a + b := by
  simp [foo]

#print ex1

def bla (b : Bool) (f g : α → β) (a : α) : β :=
  (match b with
   | true => f | false => g) a

theorem ex2 (h : b = false) : bla b (fun x => x + 1) id 10 = 10 := by
  simp [bla, h]

#print ex2
