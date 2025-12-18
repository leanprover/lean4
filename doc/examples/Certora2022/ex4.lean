/- What is the type of Nat? -/

#check 0
-- Nat
#check Nat
-- Type
#check Type
-- Type 1
#check Type 1
-- Type 2
#check Eq.refl 2
-- 2 = 2
#check 2 = 2
-- Prop
#check Prop
-- Type

example : Prop = Sort 0   := rfl
example : Type = Sort 1   := rfl
example : Type 1 = Sort 2 := rfl
