

namespace Foo

structure A :=
(x : Nat)

def A.doubleX (a : A) :=
2 * a.x

structure B extends A :=
(y : Nat)

def f (b : B) : Nat :=
b.x + b.doubleX

theorem ex1 : { x := 10, y := 0 : B }.doubleX = 20 :=
rfl

theorem ex2 : f { x := 10, y := 0 } = 30 :=
rfl

end Foo
