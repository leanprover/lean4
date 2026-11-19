def BV (n : Nat) := { a : Array Bool // a.size = n }

axiom foo {n m : Nat} (a : BV n) (b : BV m) : BV (n - m)

def test (x1 : BV 30002) (x2 : BV 30001) (y1 : BV 60004) (y2 : BV 60003) : Prop :=
  foo x1 x2 = without_expected_type foo y1 y2

@[elab_without_expected_type]
axiom foo2 {n m : Nat} (a : BV n) (b : BV m) : BV (n - m)

def test2 (x1 : BV 30002) (x2 : BV 30001) (y1 : BV 60004) (y2 : BV 60003) : Prop :=
  foo2 x1 x2 = foo2 y1 y2
