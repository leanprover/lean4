def f [Add α] (a : α) : α :=
  a + a

def BV (n : Nat) := { a : Array Bool // a.size = n }

def allZero (bv : BV n) : Prop :=
  ∀ i, i < n → bv.val[i] = false

def foo (b : BV n) (h : allZero b) : BV n :=
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

def g1 {α : Type u} (a : α) : α :=
  a

#check g1

set_option autoBoundImplicitLocal false in
def g2 {α : Type u /- Error -/} (a : α) : α :=
  a

def g3 {α : Type β /- Error greek letters are not valid auto names for universe -/} (a : α) : α :=
  a

def g4 {α : Type v} (a : α) : α :=
  a

def g5 {α : Type (v+1)} (a : α) : α :=
  a

def g6 {α : Type u} (a : α) :=
  let β : Type u := α
  let x : β := a
  x

inductive M (m : Type v → Type w) where
  | f (β : Type v) : M m

variable {m : Type u → Type u}

def h1 (a : m α) := a

#print h1
