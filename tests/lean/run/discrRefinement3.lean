inductive Mem (a : α) : List α → Prop where
  | head {as} : Mem a (a::as)
  | tail {as} : Mem a as → Mem a (a'::as)

infix:50 " ∈ " => Mem

example (a b : Nat) (h : a ∈ [b]) : b = a :=
  match h with
  | Mem.head => rfl

example {as : List α} (h : a ∈ b :: as) : b = a ∨ a ∈ as :=
  match h with
  | Mem.head    => Or.inl rfl
  | Mem.tail h' => Or.inr h'

example (a b : Nat) (h : a.succ.succ = b.succ.succ.succ) : a = b.succ :=
  match h with
  | rfl => rfl

inductive Vec (α : Type u) : Nat → Type u where
  | nil  : Vec α 0
  | cons : α → Vec α n → Vec α (n + 1)

def hv (xs : Vec Nat (n+1)) : Nat :=
  match xs with
  | Vec.cons a .. => a

def addHead (p : Vec Nat n × Vec Nat n) : Nat :=
  match p with
  | (Vec.cons a _, Vec.cons b _) => a + b
  | (Vec.nil, Vec.nil) => 0

inductive HVec : {n : Nat} → Vec (Type u) n → Type (u+1)
  | nil  : HVec Vec.nil
  | cons : {αs : Vec (Type u) n} → α → HVec αs → HVec (Vec.cons α αs)

abbrev HVec.TypeHead {αs : Vec (Type u) n} (xs : HVec αs) : Type u :=
  match xs with
  | HVec.nil => PUnit
  | HVec.cons (α := α) .. => α

def HVec.head {αs : Vec (Type u) n} (xs : HVec αs) : TypeHead xs :=
  match xs with
  | HVec.cons a _ => a
  | HVec.nil      => PUnit.unit
