import .types.trunc 
open eq bool equiv sigma sigma.ops trunc is_trunc pi

section

  universe variable u

  -- 3.8.1. The axiom of choice.
  definition AC := Π (X : Type.{u}) (A : X -> Type.{u}) (P : Π x, A x -> Type.{u}),
  is_hset X -> (Π x, is_hset (A x)) -> (Π x a, is_hprop (P x a)) ->
  (Π x, ∥ Σ a, P x a ∥) -> ∥ Σ f, Π x, P x (f x) ∥

  -- 3.8.3. Corresponds to the assertion that "the cartesian product of a family of nonempty sets is nonempty".
  definition AC_cart := Π (X : Type.{u}) (A : X -> Type.{u}), 
  is_hset X -> (Π x, is_hset (A x)) -> (Π x, ∥ A x ∥) -> ∥ Π x, A x ∥  

  -- A slight variant of AC with a modified (equivalent) codomain.
  definition AC' := Π (X : Type.{u}) (A : X -> Type.{u}) (P : Π x, A x -> Type.{u}),
  is_hset X -> (Π x, is_hset (A x)) ->  (Π x a, is_hprop (P x a))
  -> (Π x, ∥ Σ a, P x a ∥) -> ∥ Π x, Σ a : A x, P x a ∥

  -- The equivalence of AC and AC' follows from the equivalence of their codomains.
  definition AC_equiv_AC' : AC.{u} ≃ AC'.{u} :=
  @equiv_of_is_hprop _ _ !is_trunc_pi !is_trunc_pi
  (λ H X A P HX HA HP HI, trunc_functor _
  (to_fun !sigma_pi_equiv_pi_sigma) (H X A P HX HA HP HI))
  (λ H X A P HX HA HP HI, trunc_functor _
  (to_inv !sigma_pi_equiv_pi_sigma) (H X A P HX HA HP HI))

  -- AC_cart can be derived from AC' by setting P := λ _ _ , unit.
  definition AC_cart_of_AC' : AC'.{u} -> AC_cart.{u} :=
  λ H X A HX HA HI, trunc_functor _ (λ H0 x, (H0 x).1) 
  (H X A (λ x a, lift.{0 u} unit) HX HA (λ x a, !is_trunc_lift) 
  (λ x, trunc_functor _ (λ a, ⟨a, lift.up.{0 u} unit.star⟩) (HI x))) 

  -- And the converse, by setting A := λ x, Σ a, P x a.
  definition AC'_of_AC_cart : AC_cart.{u} -> AC'.{u} :=
  by intro H X A P HX HA HP HI;
  apply H X (λ x, Σ a, P x a) HX (λ x, !is_trunc_sigma) HI
  
  -- Which is enough to show AC' ≃ AC_cart, since both are hprops. 
  definition AC'_equiv_AC_cart : AC'.{u} ≃ AC_cart.{u} :=
  @equiv_of_is_hprop _ _ !is_trunc_pi !is_trunc_pi AC'_to_AC_cart.{u} AC_cart_to_AC'.{u}

  -- 3.8.2. AC ≃ AC_cart follows by transitivity. 
  definition AC_equiv_AC_cart : AC.{u} ≃ AC_cart.{u} := 
  equiv.trans AC_equiv_AC' AC'_equiv_AC_cart


  definition X : Type.{1} := Σ A : Type.{0}, ∥ A = bool ∥
  
  definition x0 : X := ⟨bool, merely.intro _ rfl⟩

  definition Y : X -> Type.{1} := λ x, x0 = x

  definition not_is_hprop_bool_eq_bool : ¬ is_hprop (bool = bool) :=
  λ H, eq_bnot_ne_idp !is_hprop.elim 

  definition not_is_hset_X : ¬ is_hset X := 
  begin
    intro H, apply not_is_hprop_bool_eq_bool,
    apply @is_trunc_equiv_closed (x0 = x0),
    apply equiv.symm !equiv_subtype
  end 

  definition is_hset_bool : is_hset bool :=
  @is_hset_of_decidable_eq _ bool.has_decidable_eq

  definition is_hset_x1 (x : X) : is_hset x.1 :=
  by cases x; induction a_1; apply a_1⁻¹ ▸ is_hset_bool

  definition is_hset_Yx (x : X) : is_hset (Y x) :=
  begin
    apply @is_trunc_equiv_closed _ _ _ !equiv_subtype,
    apply @is_trunc_equiv_closed _ _ _ (equiv.symm !eq_equiv_equiv), 
    apply is_trunc_equiv; repeat (apply is_hset_x1)
  end

  definition trunc_Yx (x : X) : ∥ Y x ∥ := 
  begin
    cases x, induction a_1, apply merely.intro,
    apply to_fun !equiv_subtype, rewrite a_1
  end

  -- 3.8.5. There exists a type X and a family Y : X → U such that each Y(x) is a set, but such that (3.8.3) is false.
  definition X_must_be_hset : Σ (X : Type.{1}) (Y : X -> Type.{1})
  (HA : Π x : X, is_hset (Y x)), ¬ ((Π x : X, ∥ Y x ∥) -> ∥ Π x : X, Y x ∥) :=
  ⟨X, Y, is_hset_Yx, λ H, trunc.rec_on (H trunc_Yx)
  (λ H0, not_is_hset_X (@is_trunc_of_is_contr _ _ (is_contr.mk x0 H0)))⟩ 

end
