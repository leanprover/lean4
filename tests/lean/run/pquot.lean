import logic.cast data.list data.sigma

-- The (pre-)quotient type kernel extension would add the following constants
--    quot, pquot.mk, pquot.eqv and pquot.rec
-- and a computational rule, which we call pquot.comp here.
-- Note that, these constants do not assume the environment contains =
constant pquot.{l} {A : Type.{l}} (R : A → A → Prop) : Type.{l}

constant pquot.abs  {A : Type} (R : A → A → Prop) : A → pquot R
-- pquot.eqv is a way to say R a b → (pquot.abs R a) = (pquot.abs R b) without mentioning equality
constant pquot.eqv {A : Type} (R : A → A → Prop) {a b : A} : R a b → ∀ (P : pquot R → Prop), P (pquot.abs R a) → P (pquot.abs R b)
constant pquot.rec {A : Type} {R : A → A → Prop} {C : pquot R → Type}
                  (f : Π a, C (pquot.abs R a))
                  -- sound is essentially saying: ∀ (a b : A) (H : R a b), f a == f b
                  -- H makes sure we can only define a function on (quot R) if for all a b : A
                  --  R a b → f a == f b
                  (sound : ∀ a b, R a b → ∀ P : (Π (q : pquot R), C q → Prop), P (pquot.abs R a) (f a) → P (pquot.abs R b) (f b))
                  (q : pquot R)
                  : C q
-- We would also get the following computational rule:
--    pquot.rec R H₁ H₂ (pquot.abs R a) ==> H₁ a
constant pquot.comp {A : Type} {R : A → A → Prop} {C : pquot R → Type}
                   (f : Π a, C (pquot.abs R a))
                   (sound : ∀ a b, R a b → ∀ P : (Π (q : pquot R), C q → Prop), P (pquot.abs R a) (f a) → P (pquot.abs R b) (f b))
                   (a : A)
                   -- In the implementation this would be a computational rule
                   : pquot.rec f sound (pquot.abs R a) = f a

-- If the environment contains = and ==, then we can define

definition pquot.eq {A : Type} (R : A → A → Prop) {a b : A} (H : R a b) : pquot.abs R a = pquot.abs R b :=
have aux : ∀ (P : pquot R → Prop), P (pquot.abs R a) → P (pquot.abs R b), from
  pquot.eqv R H,
aux (λ x : pquot R, pquot.abs R a = x) rfl

definition pquot.rec_on {A : Type} {R : A → A → Prop} {C : pquot R → Type}
                        (q : pquot R)
                        (f : Π a, C (pquot.abs R a))
                        (sound : ∀ (a b : A), R a b → f a == f b)
                        : C q :=
pquot.rec f
  (λ (a b : A) (H : R a b) (P : Π (q : pquot R), C q → Prop) (Ha : P (pquot.abs R a) (f a)),
    have aux₁ : f a == f b, from sound a b H,
    have aux₂ : pquot.abs R a = pquot.abs R b, from pquot.eq R H,
    have aux₃ : ∀ (c₁ c₂ : C (pquot.abs R a)) (e : c₁ == c₂), P (pquot.abs R a) c₁ → P (pquot.abs R a) c₂, from
      λ c₁ c₂ e H, eq.rec_on (heq.to_eq e) H,
    have aux₄ : ∀ (c₁ : C (pquot.abs R a)) (c₂ : C (pquot.abs R b)) (e : c₁ == c₂), P (pquot.abs R a) c₁ → P (pquot.abs R b) c₂, from
      eq.rec_on aux₂ aux₃,
    show P (pquot.abs R b) (f b), from
      aux₄ (f a) (f b) aux₁ Ha)
  q

definition pquot.lift {A : Type} {R : A → A → Prop} {B : Type}
                      (f : A → B)
                      (sound : ∀ (a b : A), R a b → f a = f b)
                      (q : pquot R)
                      : B :=
pquot.rec_on q f (λ (a b : A) (H : R a b), heq.of_eq (sound a b H))

theorem pquot.induction_on {A : Type} {R : A → A → Prop} {P : pquot R → Prop}
                           (q : pquot R)
                           (f : ∀ a, P (pquot.abs R a))
                           : P q :=
pquot.rec_on q f (λ (a b : A) (H : R a b),
  have aux₁ : pquot.abs R a = pquot.abs R b,         from pquot.eq R H,
  have aux₂ : P (pquot.abs R a) = P (pquot.abs R b), from congr_arg P aux₁,
  have aux₃ : cast aux₂ (f a) = f b,             from proof_irrel (cast aux₂ (f a)) (f b),
  show f a == f b, from
    @cast_to_heq _ _ _ _ aux₂ aux₃)

theorem pquot.abs.surjective {A : Type} {R : A → A → Prop} : ∀ q : pquot R, ∃ x : A, pquot.abs R x = q :=
take q, pquot.induction_on q (take a, exists.intro a rfl)

definition pquot.exact {A : Type} (R : A → A → Prop) :=
∀ a b : A, pquot.abs R a = pquot.abs R b → R a b

-- Definable quotient
structure dquot {A : Type} (R : A → A → Prop) :=
mk :: (rep : pquot R → A)
      (complete : ∀a, R (rep (pquot.abs R a)) a)
      -- (stable : ∀q, pquot.abs R (rep q) = q)

structure is_equiv {A : Type} (R : A → A → Prop) :=
mk :: (refl  : ∀x, R x x)
      (symm  : ∀{x y}, R x y → R y x)
      (trans : ∀{x y z}, R x y → R y z → R x z)

-- Definiable quotients are exact if R is an equivalence relation
theorem quot_exact {A : Type} {R : A → A → Prop} (eqv : is_equiv R) (q : dquot R) : pquot.exact R :=
λ (a b : A) (H : pquot.abs R a = pquot.abs R b),
  have H₁ : pquot.abs R a = pquot.abs R a → R (dquot.rep q (pquot.abs R a)) (dquot.rep q (pquot.abs R a)),
    from λH, is_equiv.refl eqv _,
  have H₂ : pquot.abs R a = pquot.abs R b → R (dquot.rep q (pquot.abs R a)) (dquot.rep q (pquot.abs R b)),
    from eq.subst H H₁,
  have H₃ : R (dquot.rep q (pquot.abs R a)) (dquot.rep q (pquot.abs R b)),
    from H₂ H,
  have H₄ : R a (dquot.rep q (pquot.abs R a)), from is_equiv.symm eqv (dquot.complete q a),
  have H₅ : R (dquot.rep q (pquot.abs R b)) b, from dquot.complete q b,
  is_equiv.trans eqv H₄ (is_equiv.trans eqv H₃ H₅)
