module

public section
set_option trace.Meta.isDefEq true
structure A := a : Nat

#print A.rec
#print A.mk
theorem t : sizeOf (A.mk a) = 1 + sizeOf a := (rfl)
theorem t2 : sizeOf (A.mk a) = 1 + sizeOf a := rfl

structure B extends A := b : Nat

def B.a (self : B) := self.a + self.b

private def B.a (self : B) := self.a + self.b

namespace B
  def a (self : B) := self.a + self.b
end B

def b : B := {a := 1, b := 2}

#eval b.a -- 1
