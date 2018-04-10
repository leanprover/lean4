variable {A : Type}

structure has_refl (R : A → A → Prop) : Prop :=
(refl : ∀ a, R a a)
namespace test
structure is_equiv (R : A → A → Prop) extends has_refl R : Prop :=
(symm : ∀ a b, R a b → R b a)
(trans : ∀ a b c, R a b → R b c → R a c)

#check @has_refl.refl
#check @is_equiv.symm
#check @is_equiv.trans
#check @is_equiv.to_has_refl
end test
