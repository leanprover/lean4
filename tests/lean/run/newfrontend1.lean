def x := 1

new_frontend

#check x

variables {α : Type}

def f (a : α) : α :=
a

def tst (xs : List Nat) : Nat :=
xs.foldl (init := 10) (· + ·)

#check tst [1, 2, 3]

#check tst

#check (fun stx => if True then let e := stx; HasPure.pure e else HasPure.pure stx : Nat → Id Nat)

#check let x : Nat := 1; x
