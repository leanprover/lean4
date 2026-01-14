inductive Formula : Nat → Type u where
  | bot                            : Formula n
  | imp (f₁ f₂ : Formula     n   ) : Formula n
  | all (f     : Formula    (n+1)) : Formula n

def Formula.count_quantifiers : {n:Nat} → Formula n → Nat
  | _, imp f₁ f₂ => f₁.count_quantifiers + f₂.count_quantifiers
  | _, all f => f.count_quantifiers + 1
  | _, _ => 0

attribute [simp] Formula.count_quantifiers

/--
info: Formula.count_quantifiers.eq_1.{u_1} (x✝ : Nat) (f₁ f₂ : Formula x✝) :
  (f₁.imp f₂).count_quantifiers = f₁.count_quantifiers + f₂.count_quantifiers
-/
#guard_msgs in
#check Formula.count_quantifiers.eq_1

/--
info: Formula.count_quantifiers.eq_2.{u_1} (x✝ : Nat) (f : Formula (x✝ + 1)) :
  f.all.count_quantifiers = f.count_quantifiers + 1
-/
#guard_msgs in
#check Formula.count_quantifiers.eq_2

/--
info: Formula.count_quantifiers.eq_3.{u_1} (x✝ : Nat) (x✝¹ : Formula x✝)
  (x_4 : ∀ (f₁ f₂ : Formula x✝), x✝¹ = f₁.imp f₂ → False) (x_5 : ∀ (f : Formula (x✝ + 1)), x✝¹ = f.all → False) :
  x✝¹.count_quantifiers = 0
-/
#guard_msgs in
#check Formula.count_quantifiers.eq_3

@[simp] def Formula.count_quantifiers2 : Formula n → Nat
  | imp f₁ f₂ => f₁.count_quantifiers2 + f₂.count_quantifiers2
  | all f     => f.count_quantifiers2 + 1
  | _         => 0
