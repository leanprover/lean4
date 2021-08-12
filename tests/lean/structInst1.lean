structure A where
  x : Nat
  w : Nat

structure B extends A where
  y : Nat

structure C extends B where
  z : Nat

def f1 (c : C) (a : A) : C :=
  { c with toA := a, x := 0 }  -- Error, `toA` and `x` are both updates to field `x`

def f2 (c : C) (a : A) : C :=
  { c with toA := a }

def f3 (c : C) (a : A) : C :=
  { a, c with x := 0 }

theorem ex1 (a : A) (c : C) : (f3 c a).x = 0 :=
  rfl

theorem ex2 (a : A) (c : C) : (f3 c a).w = a.w :=
  rfl

def f4 (c : C) (a : A) : C :=
  { c, a with x := 0 } -- TODO: generate error that `a` was not used?

theorem ex3 (a : A) (c : C) : (f4 c a).w = c.w :=
  rfl

theorem ex4 (a : A) (c : C) : (f4 c a).x = 0 :=
  rfl

def f5 (c : C) (a : A) :=
  { c, a with x := 0 } -- Error
