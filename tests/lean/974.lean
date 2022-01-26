inductive Formula : Nat → Type u
| bot                            : Formula n
| imp (f₁ f₂ : Formula     n   ) : Formula n
| all (f     : Formula    (n+1)) : Formula n

def Formula.count_quantifiers : {n:Nat} → Formula n → Nat
| _, imp f₁ f₂ => f₁.count_quantifiers + f₂.count_quantifiers
| _, all f => f.count_quantifiers + 1
| _, _ => 0

attribute [simp] Formula.count_quantifiers

#check @Formula.count_quantifiers._eq_1
#check @Formula.count_quantifiers._eq_2
#check @Formula.count_quantifiers._eq_3
