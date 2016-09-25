open tactic

universe l
constants (A : Type.{l}) (rel : A → A → Prop)
          (rel.refl : ∀ a, rel a a)
          (rel.symm : ∀ a b, rel a b → rel b a)
          (rel.trans : ∀ a b c, rel a b → rel b c → rel a c)

attribute [refl] rel.refl
attribute [symm] rel.symm
attribute [trans] rel.trans

constants (x y z : A) (f g h : A → A)
          (H₁ : rel (f x) (g y))
          (H₂ : rel (h (g y)) z)
          (Hf : ∀ (a b : A), rel a b → rel (f a) (f b))
          (Hg : ∀ (a b : A), rel a b → rel (g a) (g b))
          (Hh : ∀ (a b : A), rel a b → rel (h a) (h b))

attribute [simp] H₁ H₂
attribute [congr] Hf Hg Hh

print [simp] simp
print [congr] congr

meta definition relsimp_core (e : expr) : tactic (expr × expr) :=
do simp_lemmas  ← mk_simp_lemmas,
   e_type       ← infer_type e >>= whnf,
   simplify_core failed `rel simp_lemmas e

example : rel (h (f x)) z :=
by do e₁ ← to_expr `(h (f x)),
      (e₁', pf) ← relsimp_core e₁,
      exact pf
