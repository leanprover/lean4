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
| mk (a : α) : Image (f a)

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
