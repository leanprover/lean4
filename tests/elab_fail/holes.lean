

def f (x : Nat) : Nat :=
id (_ x)

def g {α β : Type} (a : α) : α :=
a

def f3 (x : Nat) : Nat :=
let y := g x + g x;
y + _ + ?hole

def f4 {α β} (a : α) := a

def f5 {α} {β : _} (a : α) := a

def f6 (a : Nat) :=
let f {α β} (a : α) := a;
f a

partial def f7 (x : Nat) :=
f7 x

partial def f8 (x : Nat) :=
let rec aux (y : Nat) := aux y;
x + 1
