--

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

universe u

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

axiom someNat : Nat

noncomputable def f2 (x : Nat) := -- must mark as noncomputable since it uses axiom `someNat`
x + someNat

inductive Parity : Nat -> Type
| even (n) : Parity (n + n)
| odd  (n) : Parity (Nat.succ (n + n))

axiom nDiv2 (n : Nat)     : n % 2 = 0 → n = n/2 + n/2
axiom nDiv2Succ (n : Nat) : n % 2 ≠ 0 → n = Nat.succ (n/2 + n/2)

def parity (n : Nat) : Parity n :=
if h : n % 2 = 0 then
  Eq.ndrec (Parity.even (n/2)) (nDiv2 n h).symm
else
  Eq.ndrec (Parity.odd (n/2)) (nDiv2Succ n h).symm

partial def natToBin : (n : Nat) → List Bool
| 0 => []
| n => match n, parity n with
  | _, Parity.even j => false :: natToBin j
  | _, Parity.odd  j => true  :: natToBin j

#eval natToBin 6

partial def natToBin' : (n : Nat) → List Bool
| 0 => []
| n => match parity n with
  | Parity.even j => false :: natToBin j
  | Parity.odd  j => true  :: natToBin j

partial def natToBinBad (n : Nat) : List Bool :=
match n, parity n with
| 0, _             => []
| _, Parity.even j => false :: natToBin j
| _, Parity.odd  j => true  :: natToBin j

partial def natToBin2 (n : Nat) : List Bool :=
match n, parity n with
| _, Parity.even 0 => []
| _, Parity.even j => false :: natToBin j
| _, Parity.odd  j => true  :: natToBin j

#eval natToBin2 6

partial def natToBin2' (n : Nat) : List Bool :=
match parity n with
| Parity.even 0 => []
| Parity.even j => false :: natToBin j
| Parity.odd  j => true  :: natToBin j

#check fun (a, b) => a -- Error type of pattern variable contains metavariables

#check fun (a, b) => (a:Nat) + b

#check fun (a, b) => a && b

#check fun ((a : Nat), (b : Nat)) => a + b

#check fun
  | some a, some b => some (a + b : Nat)
  | _,      _      => none

-- overapplied matcher
#check fun x => (match x with | 0 => id | x+1 => id) x

#check fun
  | #[1, 2]    => 2
  | #[]        => 0
  | #[3, 4, 5] => 3
  | _          => 4

-- underapplied matcher
def g {α} : List α → Nat
  | [a] => 1
  | _   => 0

#check g.match_1

#check fun (e : Empty) => (nomatch e : False)
