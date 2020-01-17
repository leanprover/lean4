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

def foo (a : Nat) (b : Nat := 10) (c : Bool := Bool.true) : Nat :=
a + b

set_option pp.all true

#check foo 1

#check foo 3 (c := false)

def Nat.boo (a : Nat) :=
succ a -- succ here is resolved as `Nat.succ`.

#check Nat.boo

#check true

-- apply is still a valid identifier name
def apply := "hello"

#check apply

theorem simple (x y : Nat) (h : x = y) : x = y :=
begin
  assumption
end
