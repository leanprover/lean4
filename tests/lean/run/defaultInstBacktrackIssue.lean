class HOp (α β γ) where hOp : α → β → γ

class LOp (α β) where lOp : α → β → β

class Op (α) where op : α → α → α

@[default_instance]
instance inst1 [LOp α β] : HOp α β β := ⟨LOp.lOp⟩

instance inst2 [Op α] : LOp α α := ⟨Op.op⟩

infix:75 " ⋆ " => HOp.hOp

section Test
variable (α) [LOp Nat α]
variable (x y z : α) (m n : Nat)

example : n ⋆ x = z := sorry -- TC works

example : 1 ⋆ x = z := sorry -- TC works

attribute [default_instance] inst2

example : n ⋆ x = z := sorry -- TC works

example : 1 ⋆ x = z := sorry -- TC fails

end Test
