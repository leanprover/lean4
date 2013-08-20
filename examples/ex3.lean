Definition xor (x y : Bool) : Bool := (not x) = y
Infixr 50 ⊕ : xor
Show xor true false
Eval xor true true
Eval xor true false
Variable a : Bool
Show a ⊕ a ⊕ a
Check Subst
Theorem EM2 (a : Bool) : a \/ (not a) :=
   Case (fun x : Bool, x \/ (not x)) Trivial Trivial a
Check EM2
Check EM2 a
