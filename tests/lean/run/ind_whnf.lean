inductive Expr : id Type
  | var : Nat → Expr
  | app : String → List Expr → Expr

partial def Expr.fold (f : Nat → α → α) : Expr → α → α
  | var n,    a => f n a
  | app s as, a => as.foldl (init := a) fun a e => fold f e a

def Expr.isVar : Expr → Bool
  | var _ => true
  | _     => false

inductive Lst (α : Type u) : id (id (Type u))
  | nil : Lst α
  | cons : α → Lst α → Lst α

protected def Lst.append : Lst α → Lst α → Lst α
  | nil,       bs => bs
  | cons a as, bs => cons a (Lst.append as bs)

/--
info: inductive Lst.{u} : Type u → id (id (Type u))
number of parameters: 1
constructors:
Lst.nil : {α : Type u} → Lst α
Lst.cons : {α : Type u} → α → Lst α → Lst α
-/
#guard_msgs in
#print Lst

def Set (α : Type u) : Type u := α → Prop

mutual
  inductive Even : Set Nat
  | zero : Even 0
  | succ : Odd n → Even n

  inductive Odd : Set Nat
  | succ : Even n → Odd n
end

/--
info: inductive Even : Set Nat
number of parameters: 0
constructors:
Even.zero : Even 0
Even.succ : ∀ {n : Nat}, Odd n → Even n
-/
#guard_msgs in
#print Even

/--
info: inductive Odd : Set Nat
number of parameters: 0
constructors:
Odd.succ : ∀ {n : Nat}, Even n → Odd n
-/
#guard_msgs in
#print Odd
