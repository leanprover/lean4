definition xor (x y : Bool) : Bool := (not x) = y
infixr 50 ⊕ : xor
print xor true false
eval xor true true
eval xor true false
variable a : Bool
print a ⊕ a ⊕ a
check @Subst
theorem EM2 (a : Bool) : a \/ (not a) :=
   Case (fun x : Bool, x \/ (not x)) Trivial Trivial a
check EM2
check EM2 a
