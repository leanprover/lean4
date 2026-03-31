--

def f : List Int → Bool := fun _ => true

def ex3 : IO Bool := do
let xs ← pure [1, 2, 3];
pure $ f xs -- Works

inductive Expr
| val : Nat → Expr
| app : Expr → Expr → Expr

instance : Coe Nat Expr := ⟨Expr.val⟩
instance : OfNat Expr n where
  ofNat := Expr.val n

def foo : Expr → Expr := fun e => e

def ex1 : Bool :=
f [1, 2, 3]  -- Works

def ex2 : Bool :=
let xs := [1, 2, 3];
f xs -- Works

def ex4 :=
[1, 2, 3].map $ fun x => x+1

def ex5 (xs : List String) :=
xs.foldl (fun r x => r.push x) Array.empty

set_option pp.all true in
/-- info: foo (@OfNat.ofNat.{0} Expr (nat_lit 1) (@instOfNatExpr (nat_lit 1))) : Expr -/
#guard_msgs in
#check foo 1

def ex6 :=
foo 1
