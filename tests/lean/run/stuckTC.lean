namespace Ex1

inductive Ty where
  | int
  | bool
  | fn (a ty : Ty)

@[reducible] def Ty.interp : Ty → Type
  | int    => Int
  | bool   => Bool
  | fn a b => a.interp → b.interp

def test {a b c : Ty} (f : a.interp → b.interp → c.interp) (x : a.interp) (y : b.interp) : c.interp :=
  f x y

def f (a b : Ty.bool.interp) : Ty.bool.interp :=
  test (.==.) a b

end Ex1

namespace Ex2

inductive Ty where
  | int
  | bool

@[reducible] def Ty.interp : Ty → Type
  | int    => Int
  | bool   => Bool

def test {a b c : Ty} (f : a.interp → b.interp → c.interp) (x : a.interp) (y : b.interp) : c.interp :=
  f x y

def f (a b : Ty.bool.interp) : Ty.bool.interp :=
  test (.==.) a b

end Ex2

namespace Ex3

inductive Ty where
  | int
  | bool

@[reducible] def Ty.interp (ty : Ty) : Type :=
  Ty.casesOn (motive := fun _ => Type) ty Int Bool

/-
The discrimination tree module does not perform iota reduction. Thus, it does
not reduce the definition above, and we cannot synthesize `BEq Ty.bool.interp`.
We can workaround using `match` as in the ex
-/

def test {a b c : Ty} (f : a.interp → b.interp → c.interp) (x : a.interp) (y : b.interp) : c.interp :=
  f x y

def f (a b : Ty.bool.interp) : Ty.bool.interp :=
  test (.==.) a b

end Ex3
