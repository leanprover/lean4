class AddGroup (A : Type u) extends Zero A where
  gsmul : Int → A → A
  gsmul_zero' : ∀ a, gsmul 0 a = 0

class Ring (R : Type u) extends Zero R, AddGroup R

#print Ring.mk

#check {
  zero := 0
  gsmul := fun x n => x.toNat * n
  gsmul_zero' := fun a => Nat.zero_mul _
  : Ring Nat
}
