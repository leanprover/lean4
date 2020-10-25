

structure A :=
(a : Nat)

structure B :=
(a : Nat)

structure C :=
(a : Nat)

instance : Coe A B := ⟨fun s => ⟨s.1⟩⟩

instance : Coe A C := ⟨fun s => ⟨s.1⟩⟩

def f {α} (a b : α) := a
def forceB {α} (b : B) (a : α) := a
def forceC {α} (c : C) (a : α) := a
def forceA {α} (a : A) (o : α) := o

def f1 (x : _) (y : _) (z : _) :=
let a1 := f x y;
let a2 := f y z;
forceB x a1 -- works

def f2 (x : _) (y : _) (z : _) :=
let a1 := f x (coe y);
let a2 := f (coe y) z;
forceB x (forceC z (forceA y (a1, a2))) -- works because we manually added the coercions above

#exit

def f3 (x : _) (y : _) (z : _) :=
let a1 := f x y;
let a2 := f y z;
/- Fails because we "missed" the opportunity to insert coercions around `y`.
   I think we should **not** support this kind of example. -/
forceB x (forceC z (forceA y (a1, a2)))
