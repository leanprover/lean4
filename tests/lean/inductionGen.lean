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

def Vec.head (xs : Vec α (n+1)) : α :=
  match xs with
  | cons x _ => x

theorem ex1 (xs ys : Vec α (n+1)) (h : xs = ys) : xs.head = ys.head := by
  induction xs -- error, use cases

theorem ex2 (xs ys : Vec α (n+1)) (h : xs = ys) : xs.head = ys.head := by
  cases xs with
  | cons x xs =>
    trace_state -- `h` has been refined
    repeat admit

inductive ExprType where
  | bool  : ExprType
  | nat   : ExprType

inductive Expr : ExprType → Type
  | natVal : Nat → Expr ExprType.nat
  | boolVal : Bool → Expr ExprType.bool
  | eq : Expr α → Expr α → Expr ExprType.bool
  | add : Expr ExprType.nat → Expr ExprType.nat → Expr ExprType.nat

def constProp : Expr α → Expr α
  | Expr.add a b =>
    match constProp a, constProp b with
   | Expr.natVal v, Expr.natVal w => Expr.natVal (v + w)
   | a, b => Expr.add a b
  | e => e

abbrev denoteType : ExprType → Type
  | ExprType.bool => Bool
  | ExprType.nat  => Nat

instance : BEq (denoteType α) where
  beq a b :=
    match α, a, b with
    | ExprType.bool, a, b => a == b
    | ExprType.nat,  a, b => a == b

def eval : Expr α → denoteType α
  | Expr.natVal v  => v
  | Expr.boolVal b => b
  | Expr.eq a b    => eval a == eval b
  | Expr.add a b   => eval a + eval b

theorem ex3 (a b : Expr α) (h : a = b) : eval (constProp a) = eval b := by
  set_option trace.Meta.debug true in
  induction a
  trace_state -- b's type must have been refined, `h` too
  repeat admit

inductive Foo : Nat → Nat → Type where
  | mk : Foo 1 2

theorem ex4 (n m : Nat) (heq : n = m) (h : Foo n m) : False := by
  induction h using Foo.rec
  case mk => contradiction

theorem ex5 (n : Nat) (h : Foo n n) : False := by
  induction h using Foo.rec -- error, target repeated
