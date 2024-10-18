class AddGroup (α : Type u) extends Add α, Zero α, Neg α where
  addAssoc : {a b c : α} → a + b + c = a + (b + c)
  zeroAdd  : {a : α} → 0 + a = a
  addZero  : {a : α} → a + 0 = a
  negAdd   : {a : α} → -a + a = 0

open AddGroup

theorem negZero [AddGroup α] : -(0 : α) = 0 := by
  rw [←addZero (a := -(0 : α)), negAdd]

theorem subZero [AddGroup α] {a : α} : a + -(0 : α) = a := by
  rw [← addZero (a := a)]
  rw [addAssoc]
  rw [negZero]
  rw [addZero]

theorem shouldFail [AddGroup α] : ((0 : α) + 0) = 0 :=
  rfl -- Error
