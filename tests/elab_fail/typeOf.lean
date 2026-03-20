--

def f1 (x : Nat) (b : Bool) : type_of% x :=
let r : type_of% (x+1) := x+1;
r + 1

theorem ex1 : f1 1 true = 3 :=
rfl

def f2 (x : Nat) (b : Bool) : type_of% x :=
let r : type_of% b := x+1; -- error
r + 1

def f3 (x : Nat) (b : Bool) : type_of% b :=
let r (x!1 : type_of% x) : type_of% b := x > 1;
r x

def f4 (x : Nat) : Nat :=
let y : Nat := x
let y := ensure_type_of% y "invalid reassignment, term" y == 1 -- error
y + 1

def f5 (x : Nat) : Nat :=
let y : Nat := x
let y := ensure_type_of% y "invalid reassignment, term" (y+1)
y + 1

def f6 (x : Nat) : Nat :=
ensure_expected_type% "natural number expected, value" true
