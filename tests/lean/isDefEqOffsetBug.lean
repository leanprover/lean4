class Zero (α : Type u) where
  zero : α

export Zero (zero)

instance [Zero α] : OfNat α (nat_lit 0) where
  ofNat := zero

class AddGroup (α : Type u) extends Add α, Zero α, Neg α where
  add_assoc : {a b c : α} → a + b + c = a + (b + c)
  zero_add  : {a : α} → 0 + a = a
  add_zero  : {a : α} → a + 0 = a
  neg_add   : {a : α} → -a + a = 0

open AddGroup

theorem neg_zero [AddGroup α] : -(0 : α) = 0 := by
  rw [←add_zero (a := -(0 : α)), neg_add]

theorem sub_zero [AddGroup α] {a : α} : a + -(0 : α) = a := by
  rw [← add_zero (a := a)]
  rw [add_assoc]
  rw [neg_zero]
  rw [add_zero]

theorem should_fail [AddGroup α] : ((0 : α) + 0) = 0 :=
  rfl -- Error
