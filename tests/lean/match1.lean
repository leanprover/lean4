new_frontend

#print "---- h1"

def h1 (b : Bool) : Nat :=
match b with
| true  => 0
| false => 10

#eval h1 false

#print "---- h2"

def h2 (x : List Nat) : Nat :=
match x with
| [x1, x2] => x1 + x2
| x::xs    => x
| _        => 0

#eval h2 [1, 2]
#eval h2 [10, 4, 5]
#eval h2 []

#print "---- h3"

def h3 (x : Array Nat) : Nat :=
match x with
| #[x]    => x
| #[x, y] => x + y
| xs      => xs.size

#eval h3 #[10]
#eval h3 #[10, 20]
#eval h3 #[10, 20, 30, 40]

#print "---- inv"

inductive Image {α β : Type} (f : α → β) : β → Type
| mk (a : α) : Image f (f a)

def mkImage {α β : Type} (f : α → β) (a : α) : Image f (f a) :=
Image.mk a

def inv {α β : Type} {f : α → β} {b : β} (t : Image f b) : α :=
match b, t with
| _, Image.mk a => a

#eval inv (mkImage Nat.succ 10)

theorem foo {p q} (h : p ∨ q) : q ∨ p :=
match h with
| Or.inl h => Or.inr h
| Or.inr h => Or.inl h

def f (x : Nat × Nat) : Bool × Bool × Bool → Nat :=
match x with
| (a, b) => fun _ => a

structure S :=
(x y z : Nat := 0)

def f1 : S → S :=
fun { x := x, ..} => { y := x }

theorem ex2 : f1 { x := 10 } = { y := 10 } :=
rfl

universes u

inductive Vec (α : Type u) : Nat → Type u
| nil : Vec α 0
| cons {n} (head : α) (tail : Vec α n) : Vec α (n+1)

inductive VecPred {α : Type u} (P : α → Prop) : {n : Nat} → Vec α n → Prop
| nil   : VecPred P Vec.nil
| cons  {n : Nat} {head : α} {tail : Vec α n} : P head → VecPred P tail → VecPred P (Vec.cons head tail)

theorem ex3 {α : Type u} (P : α → Prop) : {n : Nat} → (v : Vec α (n+1)) → VecPred P v → Exists P
| _, Vec.cons head _, VecPred.cons h _ => ⟨head, h⟩

theorem ex4 {α : Type u} (P : α → Prop) : {n : Nat} → (v : Vec α (n+1)) → VecPred P v → Exists P
| _, Vec.cons head _, VecPred.cons h (w : VecPred P Vec.nil) => ⟨head, h⟩  -- ERROR
