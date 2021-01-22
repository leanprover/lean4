def myid (a : α) := a -- works

#check myid 10
#check myid true

theorem ex1 (a : α) : myid a = a := rfl

def cnst (b : β) : α → β := fun _ => b -- works

theorem ex2 (b : β) (a : α) : cnst b a = b := rfl

def Vec (α : Type) (n : Nat) := { a : Array α // a.size = n }

def mkVec : Vec α 0 := ⟨ #[], rfl ⟩

def Vec.map (xs : Vec α n) (f : α → β) : Vec β n :=
  ⟨ xs.val.map f, sorry ⟩

/- unbound implicit locals must be greek or lower case letters followed by numerical digits -/
def Vec.map2 (xs : Vec α size /- error: unknown identifier size -/) (f : α → β) : Vec β n :=
  ⟨ xs.val.map f, sorry ⟩

set_option autoBoundImplicitLocal false in
def Vec.map3 (xs : Vec α n) (f : α → β) : Vec β n := -- Errors, unknown identifiers 'α', 'n', 'β'
  ⟨ xs.val.map f, sorry ⟩

def double [Add α] (a : α) := a + a

variable (xs : Vec α n) -- works

def f := xs

#check @f

#check f mkVec

#check f (α := Nat) mkVec

def g (a : α) := xs.val.push a

theorem ex3 : g ⟨#[0], rfl⟩ 1 = #[0, 1] :=
  rfl

inductive Tree (α β : Type) :=
  | leaf1 : α → Tree α β
  | leaf2 : β → Tree α β
  | node : Tree α β → Tree α β → Tree α β

inductive TreeElem1 : α → Tree α β → Prop
  | leaf1     : (a : α) → TreeElem1 a (Tree.leaf1 (β := β) a)
  | nodeLeft  : (a : α) → (left : Tree α β) → (right : Tree α β) → TreeElem1 a left  → TreeElem1 a (Tree.node left right)
  | nodeRight : (a : α) → (left : Tree α β) → (right : Tree α β) → TreeElem1 a right → TreeElem1 a (Tree.node left right)

inductive TreeElem2 : β → Tree α β → Prop
  | leaf2     : (b : β) → TreeElem2 b (Tree.leaf2 (α := α) b)
  | nodeLeft  : (b : β) → (left : Tree α β) → (right : Tree α β) → TreeElem2 b left  → TreeElem2 b (Tree.node left right)
  | nodeRight : (b : β) → (left : Tree α β) → (right : Tree α β) → TreeElem2 b right → TreeElem2 b (Tree.node left right)

namespace Ex1

def findSomeRevM? [Monad m] (as : Array α) (f : α → m (Option β)) : m (Option β) :=
  pure none

def findSomeRev? (as : Array α) (f : α → Option β) : Option β :=
  Id.run <| findSomeRevM? as f

end Ex1

def apply {α : Type u₁} {β : α → Type u₂} (f : (a : α) → β a) (a : α) : β a :=
  f a

def pair (a : α₁) := (a, a)
