-- The following fails in the old elaborator
-- theorem tst1 : (fun a b => Nat.add a b) = Nat.add :=
-- Eq.refl (fun a b => Nat.add a b)



theorem tst2 : (fun a b => Nat.add a b) = Nat.add :=
Eq.refl (fun a b => Nat.add a b)

theorem tst3 : (fun a b => Nat.add a b) = Nat.add :=
rfl

theorem tst4 : Nat.add = (fun a b => Nat.add a b) :=
rfl

theorem tst5 : Nat.add = (fun (a b : Nat) => a + b) :=
rfl

theorem tst6 : Nat.add = (· + ·) :=
rfl

theorem tst7 : (· + ·) = Nat.add :=
rfl

theorem tst8 : (· + ·) = @Add.add Nat _ :=
rfl

theorem tst9 : (Nat.add · ·) = @Add.add Nat _ :=
rfl

axiom p    : (Nat → Nat → Nat) → Prop
axiom pAdd : p Nat.add

theorem tst10 : p (fun a b => Nat.add a b) :=
pAdd
