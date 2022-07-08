mutual
inductive Foo
 | somefoo : Foo
 | bar : Bar → Foo

inductive Bar
 | somebar : Bar
 | foobar : Foo → Bar → Bar
end

mutual
  private def Foo.toString : Foo → String
    | Foo.somefoo => "foo"
    | Foo.bar b => Bar.toString b

  def _root_.Bar.toString : Bar → String
    | Bar.somebar => "bar"
    | Bar.foobar f b => Foo.toString f ++ Bar.toString b
end

namespace Ex2
mutual
inductive Foo
 | somefoo : Foo
 | bar : Bar → Foo → Foo

inductive Bar
 | somebar : Bar
 | foobar : Foo → Bar → Bar
end

mutual
  private def Foo.toString : Foo → String
    | Foo.somefoo => go 2 ++ toString.go 2 ++ Foo.toString.go 2
    | Foo.bar b f => toString f ++ Bar.toString b
  where
    go (x : Nat) := s!"foo {x}"

  private def _root_.Ex2.Bar.toString : Bar → String
    | Bar.somebar => "bar"
    | Bar.foobar f b => Foo.toString f ++ Bar.toString b
end
end Ex2

def Nat.fact : Nat → Nat
  | 0 => 1
  | n+1 => (n+1) * Nat.fact n

example : Nat.fact 3 = 6 := rfl

namespace Boo
  def fact : Nat → Nat
  | 0 => 2
  | n+1 => (n+1) * Boo.fact n

  example : Boo.fact 3 = 12 := rfl
end Boo
