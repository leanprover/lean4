--

def f1 (x : Nat) (b : Bool) : typeOf% x :=
let r : typeOf% (x+1) := x+1;
r + 1

theorem ex1 : f1 1 true = 3 :=
rfl

def f2 (x : Nat) (b : Bool) : typeOf% x :=
let r : typeOf% b := x+1; -- error
r + 1

def f3 (x : Nat) (b : Bool) : typeOf% b :=
let r (x!1 : typeOf% x) : typeOf% b := x > 1;
r x

def f4 (x : Nat) : Nat :=
let y : Nat := x
let y := ensureTypeOf% y "invalid reassignment, term" y == 1 -- error
y + 1

def f5 (x : Nat) : Nat :=
let y : Nat := x
let y := ensureTypeOf% y "invalid reassignment, term" (y+1)
y + 1

def f6 (x : Nat) : Nat :=
ensureExpectedType% "natural number expected, value" true
