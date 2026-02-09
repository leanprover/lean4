

def f (x : Nat) (y : Nat := 1) (w : Nat := 2) (z : Nat) :=
x + y + w - z

theorem ex1 (x z : Nat) : f (z := z) x = x + 1 + 2 - z :=
rfl

theorem ex2 (x z : Nat) : f x (z := z) = x + 1 + 2 - z :=
rfl

theorem ex3 (x y : Nat) : f x y = fun z => x + y + 2 - z :=
rfl

theorem ex4 : f = (fun x z => x + 1 + 2 - z) :=
rfl

theorem ex5 (x : Nat) : f x = fun z => x + 1 + 2 - z :=
rfl

theorem ex6 (y : Nat) : f (y := 5) = fun x z => x + 5 + 2 - z :=
rfl

def g {α} [Add α] (a : α) (b? : Option α := none) (c : α) : α :=
match b? with
| none   => a + c
| some b => a + b + c

variable {α} [Add α]

theorem ex7 : g = fun (a c : α) => a + c :=
rfl

theorem ex8 (x : α) : g (c := x) = fun (a : α) => a + x :=
rfl

theorem ex9 (x : α) : g (b? := some x) = fun (a c : α) => a + x + c :=
rfl

theorem ex10 (x : α) : g x = fun (c : α) => x + c :=
rfl

theorem ex11 (x y : α) : g x y = fun (c : α) => x + y + c :=
rfl
