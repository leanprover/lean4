import tactic
definition xor (x y : Bool) : Bool := (not x) = y
infixr 50 ⊕ : xor
print xor true false
variable a : Bool
print a ⊕ a ⊕ a
check @subst
theorem EM2 (a : Bool) : a \/ (not a) :=
   case (fun x : Bool, x \/ (not x)) (by simp) (by simp) a
check EM2
check EM2 a
theorem xor_neq (a b : Bool) : (a ⊕ b) ↔ ((¬ a) = b)
:= refl (a ⊕ b)