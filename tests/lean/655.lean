structure A := a : Nat

structure B extends A := b : Nat

def B.a (self : B) := self.a + self.b

private def B.a (self : B) := self.a + self.b

namespace B
  def a (self : B) := self.a + self.b
end B

def b : B := {a := 1, b := 2}

#eval b.a -- 1
