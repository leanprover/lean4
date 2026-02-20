namespace Ex1

mutual

def Foo.boo (x : Nat) :=
  match x with
  | 0 => 1
  | x + 1 => 2*Boo.bla x

def Boo.bla (x : Nat) :=
  match x with
  | 0 => 2
  | x+1 => 3*Foo.boo x

end

example : Foo.boo 2 = 2*3*1 := by
  simp [Foo.boo, Boo.bla]

end Ex1

namespace Ex2

mutual

def Bla.Foo.boo (x : Nat) :=
  match x with
  | 0 => 1
  | x + 1 => 2*Boo.bla x

def Bla.Boo.bla (x : Nat) :=
  match x with
  | 0 => 2
  | x+1 => 3*Foo.boo x

end

example : Bla.Foo.boo 2 = 2*3*1 := by
  simp [Bla.Foo.boo, Bla.Boo.bla]

end Ex2

namespace Ex3

mutual
inductive Foo
  | somefoo : Foo
  | bar : Bar → Foo

inductive Bar
  | somebar : Bar
  | foobar : Foo → Bar → Bar
end

mutual
def Foo.toString : Foo → String
  | Foo.somefoo => "foo"
  | Foo.bar b => Bar.toString b

def Bar.toString : Bar → String
  | Bar.somebar => "bar"
  | Bar.foobar f b => (Foo.toString f) ++ (Bar.toString b)
end

end Ex3

namespace Ex4

mutual
inductive Foo
  | somefoo : Foo
  | bar : Bar → Foo

inductive Bar
  | somebar : Bar
  | foobar : Foo → Bar → Bar
end

mutual
def Foo.toString : Foo → String
  | .somefoo => "foo"
  | .bar b => b.toString

def Bar.toString : Bar → String
  | .somebar => "bar"
  | .foobar f b => f.toString ++ b.toString
end

end Ex4
