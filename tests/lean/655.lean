module

public section
structure A := a : Nat

#print A.rec
#print A.mk
#with_exporting
#reduce (types := true) fun a => sizeOf (A.mk a) = 1 + sizeOf a
theorem t : sizeOf (A.mk a) = 1 + sizeOf a := (rfl)
set_option trace.Meta.isDefEq true in
theorem t2 : sizeOf (A.mk a) = 1 + sizeOf a := rfl

structure B extends A := b : Nat

def B.a (self : B) := self.a + self.b

private def B.a (self : B) := self.a + self.b

namespace B
  def a (self : B) := self.a + self.b
end B

def b : B := {a := 1, b := 2}

#eval b.a -- 1
