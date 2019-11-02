def f : List Int → Bool := fun _ => true

def ex1 : Bool :=
f [1, 2, 3]  -- Works

def ex2 : Bool :=
let xs := [1, 2, 3];
f xs -- Works

def ex3 : IO Bool :=
do
xs ← pure [1, 2, 3];
pure $ f xs -- Works

def ex4 :=
[1, 2, 3].map $ fun x => x+1

def ex5 (xs : List String) :=
/- `r.push x` fails because we don't know the type of `r`.
   Potential solution: the elaborator should suspend the elaboration of `fun r x => r.push x`,
   elaborate `Array.empty`, and then resume the suspension.
-/
xs.foldl (fun r x => r.push x) Array.empty

inductive Expr
| val : Nat → Expr
| app : Expr → Expr → Expr

instance : HasCoe Nat Expr := ⟨Expr.val⟩

def foo : Expr → Expr := fun e => e

def ex6 :=
/- `1` is elaborated to `HasOne.one ?A ?S : ?A`.
    Typing constraints unify `?A =?= Expr`, and
    we fail to synthesize `HasOne Expr`.
    Users get confused since they have defined `HasCoe Nat Expr`.
    Solution: elaborate `1` into `Expr.lit (Literal.natVal 1) : Nat`,
    and rely on coercions.
-/
foo 1
