def f [Add α] (a : α) : α :=
  a + a

def BV (n : Nat) := { a : Array Bool // a.size = n }

def allZero (bv : BV n) : Prop :=
  ∀ i, i < n → bv.val[i] = false

def foo (n : Nat) (h : allZero b) : BV n :=
  b

def optbind (x : Option α) (f : α → Option β) : Option β :=
  match x with
  | none   => none
  | some a => f a

instance : Monad Option where
  bind := optbind
  pure := some

inductive Mem : α → List α → Prop
  | head (a : α) (as : List α) : Mem a (a::as)
