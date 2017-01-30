check { prod . fst := 10, snd := 20 }

check ({ fst := 10, snd := 20 } : nat × nat)

definition p : nat × nat :=
{ snd := 20, fst := 10 }

print p

definition attr : user_attribute :=
{ name := `foo, descr := "hello world" }

print attr

definition p2 :=
{ p with fst := 20 }

print p2

structure point :=
(x : nat) (y : nat)

structure point3d extends point :=
(z : nat)

definition p1 : point := { x := 1, y := 1 }

definition p3 : point3d := { p1 with z := 10 }

print p3

check { point3d . x := 1, y := 2, z := 3 }

check (⟨10, rfl⟩ : Σ' x : nat, x = x)

check ((| 10, rfl |) : Σ' x : nat, x = x)

check ({ fst := 10, snd := rfl } : Σ' x : nat, x = x)

definition f (a : nat) : Σ' x : nat, x = x :=
{ fst := a, snd := rfl }

print f
