class Def (α : Type u) where
  val : α

instance : Def Nat where
  val := 10

theorem ex1 : Def.val = 10 := rfl

instance (priority := default+1) : Def Nat where
  val := 20

theorem ex2 : Def.val = 20 := rfl

instance : Def Nat where
  val := 30

theorem ex3 : Def.val = 20 := rfl
