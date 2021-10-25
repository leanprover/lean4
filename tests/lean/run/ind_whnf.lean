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

#print Lst

def Set (α : Type u) : Type u := α → Prop

mutual
  inductive Even : Set Nat
  | zero : Even 0
  | succ : Odd n → Even n

  inductive Odd : Set Nat
  | succ : Even n → Odd n
end

#print Even
#print Odd
