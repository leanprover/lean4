def f (x : Nat) : Nat :=
  if h : x > 0 then
    g x + 2
  else
    1
where
  g : Nat → Nat
  | 0 => 2
  | x => f x * 2

#check! f
#check! f.g

/- Uncomment after stage0
#eval! f 0
#eval! f.g 0
-/

inductive Foo where
  | a | b | c
  deriving Repr
def h (x : Nat) : Foo :=
  match x with
  | 0 => Foo.a
  | 1 => Foo.b
  | x => h x

#check h

/- Uncomment after stage0
#eval h 0
-/
