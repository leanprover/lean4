
namespace tst
variable {A : Type}

attribute [reducible]
definition foo₁ (a b c : A) (H₁ : a = b) (H₂ : c = b) : a = c :=
eq.trans H₁ (eq.symm H₂)

lemma foo₂ (f : A → A → A) (a b c : A) (H₁ : a = b) (H₂ : c = b) : f a = f c :=
eq.symm H₂ ▸ H₁ ▸ rfl

#check foo₁
#check foo₂

end tst

#check tst.foo₁
#check tst.foo₂
#print tst.foo₁
