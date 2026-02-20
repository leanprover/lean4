

def f (x : Nat) (y : Bool) :=
x + if y then 1 else 0

def g (x y : Nat) :=
x + y

#check f ?x ?x -- error the first occurrence (?x : Nat) and the second (?x : Bool)

#check g ?x ?x -- ok

def h1 (x : Nat) : Nat := by
refine g ?hole ?hole; -- it is the same hole
case hole => exact x

#eval h1 10

theorem ex1 : h1 10 = 20 :=
rfl

def h2 (x : Nat) : Nat := by
refine g ?hole ?hole;
exact x+x

theorem ex2 : h2 10 = 40 :=
rfl

def foo (f : Nat → Nat) (x : Nat) := f x
def bla (x : Nat) (f : Nat → Nat) := f x
def boo (f : Nat → Nat) (g : Bool → Nat) := f (g true)

#check foo (fun x => ?hole) ?hole
#check bla ?hole (fun x => ?hole)
#check boo (fun x => ?hole) (fun y => ?hole) -- error the local contexts of the two holes are incompatible

def h3 (x : Nat) : Nat := by
apply boo;
case f => refine fun y => ?hole + 1; exact x;  -- `fun y => ?hole + 1` and assigned `?hole := x`
case g => refine fun b => ?hole                -- `fun b => ?hole` it works because assignment is compatible

#eval h3 10

theorem ex3 : h3 10 = 11 := rfl

def h4 (x : Nat) : Nat := by
refine foo (fun y => ?hole + 2) ?hole;
-- note that the local context of ?hole has be shrunk by the second occurrence
exact x

#eval h4 10

theorem ex4 : h4 10 = 12 := rfl

def h5 (x : Nat) : Nat := by
apply boo;
case f => intro y; refine ?hole + 1; exact y;  -- `fun y => ?hole + 1` and assigned `?hole := y`
case g => refine fun b => ?hole                -- error
