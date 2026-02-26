inductive Vec (α : Type u) : Nat → Type u
  | nil  : Vec α 0
  | cons : α → Vec α n → Vec α (n+1)

def Vec.map (xs : Vec α n) (f : α → β) : Vec β n :=
  match xs with
  | nil       => nil
  | cons a as => cons (f a) (map as f)

def Vec.map' (f : α → β) : Vec α n → Vec β n
  | nil       => nil
  | cons a as => cons (f a) (map' f as)

def Vec.map2 (f : α → α → β) : Vec α n → Vec α n → Vec β n
  | nil,       nil       => nil
  | cons a as, cons b bs => cons (f a b) (map2 f as bs)
