structure Foo.A where
  x : Nat

structure Boo.A extends Foo.A where
  y : Nat

structure B extends toA_1 : Boo.A where
  z : Nat

def f1 (x y z : Nat) : B :=
  { x, y, z }

theorem ex1 (x y z : Nat) : f1 x y z = ⟨⟨⟨x⟩, y⟩, z⟩ :=
  rfl

theorem ex2 (x y z : Nat) : f1 x y z = B.mk (Boo.A.mk (Foo.A.mk x) y) z :=
  rfl

#check { x := 0, y := 1, z := 2 : B }

structure Foo.C where
  x : Nat
  y : Nat

structure Boo.C where
  x : Nat
  z : Nat

structure D extends Foo.C, toC_1 : Boo.C

def f2 (x y z : Nat) : D :=
  { x, y, z }

theorem ex3 (x y z : Nat) : f2 x y z = D.mk ⟨x, y⟩ z :=
  rfl

#check { x := 0, y := 1, z := 2 : D }

#print D.toC_1
