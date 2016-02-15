/-
Copyright (c) 2015 Ulrik Buchholtz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ulrik Buchholtz
-/
import types.trunc types.eq types.arrow_2 types.fiber .susp

open eq is_trunc is_equiv nat equiv trunc function fiber funext

namespace homotopy

  definition is_conn [reducible] (n : trunc_index) (A : Type) : Type :=
  is_contr (trunc n A)

  definition is_conn_equiv_closed (n : trunc_index) {A B : Type}
    : A ≃ B → is_conn n A → is_conn n B :=
  begin
    intros H C,
    fapply @is_contr_equiv_closed (trunc n A) _,
    apply trunc_equiv_trunc,
    assumption
  end

  definition is_conn_map (n : trunc_index) {A B : Type} (f : A → B) : Type :=
  Πb : B, is_conn n (fiber f b)

  namespace is_conn_map
  section
    parameters {n : trunc_index} {A B : Type} {h : A → B}
               (H : is_conn_map n h) (P : B → n -Type)

    private definition rec.helper : (Πa : A, P (h a)) → Πb : B, trunc n (fiber h b) → P b :=
    λt b, trunc.rec (λx, point_eq x ▸ t (point x))

    private definition rec.g : (Πa : A, P (h a)) → (Πb : B, P b) :=
    λt b, rec.helper t b (@center (trunc n (fiber h b)) (H b))

    -- induction principle for n-connected maps (Lemma 7.5.7)
    protected definition rec : is_equiv (λs : Πb : B, P b, λa : A, s (h a)) :=
    adjointify (λs a, s (h a)) rec.g
    begin
      intro t, apply eq_of_homotopy, intro a, unfold rec.g, unfold rec.helper,
      rewrite [@center_eq _ (H (h a)) (tr (fiber.mk a idp))],
    end
    begin
      intro k, apply eq_of_homotopy, intro b, unfold rec.g,
      generalize (@center _ (H b)), apply trunc.rec, apply fiber.rec,
      intros a p, induction p, reflexivity
    end

    protected definition elim : (Πa : A, P (h a)) → (Πb : B, P b) :=
    @is_equiv.inv _ _ (λs a, s (h a)) rec

    protected definition elim_β : Πf : (Πa : A, P (h a)), Πa : A, elim f (h a) = f a :=
    λf, apd10 (@is_equiv.right_inv _ _ (λs a, s (h a)) rec f)

  end

  section
    parameters {n k : trunc_index} {A B : Type} {f : A → B}
               (H : is_conn_map n f) (P : B → (n +2+ k)-Type)

    include H
    -- Lemma 8.6.1
    proposition elim_general (t : Πa : A, P (f a))
      : is_trunc k (fiber (λs : (Πb : B, P b), (λa, s (f a))) t) :=
    begin
      induction k with k IH,
      { apply is_contr_fiber_of_is_equiv, apply is_conn_map.rec, exact H },
      { apply is_trunc_succ_intro,
        intros x y, cases x with g p, cases y with h q,
        assert e : fiber (λr : g ~ h, (λa, r (f a))) (apd10 (p ⬝ q⁻¹))
                 ≃ (fiber.mk g p = fiber.mk h q
                     :> fiber (λs : (Πb, P b), (λa, s (f a))) t),
        { apply equiv.trans !fiber.sigma_char,
          assert e' : Πr : g ~ h,
                 ((λa, r (f a)) = apd10 (p ⬝ q⁻¹))
               ≃ (ap (λv, (λa, v (f a))) (eq_of_homotopy r) ⬝ q = p),
          { intro r,
            refine equiv.trans _ (eq_con_inv_equiv_con_eq q p
                                   (ap (λv a, v (f a)) (eq_of_homotopy r))),
            rewrite [-(ap (λv a, v (f a)) (apd10_eq_of_homotopy r))],
            rewrite [-(apd10_ap_precompose_dependent f (eq_of_homotopy r))],
            apply equiv.symm,
            apply eq_equiv_fn_eq (@apd10 A (λa, P (f a)) (λa, g (f a)) (λa, h (f a))) },
          apply equiv.trans (sigma.sigma_equiv_sigma_right e'), clear e',
          apply equiv.trans (equiv.symm (sigma.sigma_equiv_sigma_left
                                           eq_equiv_homotopy)),
          apply equiv.symm, apply equiv.trans !fiber_eq_equiv,
          apply sigma.sigma_equiv_sigma_right, intro r,
          apply eq_equiv_eq_symm },
        apply @is_trunc_equiv_closed _ _ k e, clear e,
        apply IH (λb : B, trunctype.mk (g b = h b)
                           (@is_trunc_eq (P b) (n +2+ k) (trunctype.struct (P b))
                           (g b) (h b))) }
    end
  end

  section
    universe variables u v
    parameters {n : trunc_index} {A : Type.{u}} {B : Type.{v}} {h : A → B}
    parameter sec : ΠP : B → trunctype.{max u v} n,
                    is_retraction (λs : (Πb : B, P b), λ a, s (h a))

    private definition s := sec (λb, trunctype.mk' n (trunc n (fiber h b)))

    include sec

    -- the other half of Lemma 7.5.7
    definition intro : is_conn_map n h :=
    begin
      intro b,
      apply is_contr.mk (@is_retraction.sect _ _ _ s (λa, tr (fiber.mk a idp)) b),
      apply trunc.rec, apply fiber.rec, intros a p,
      apply transport
               (λz : (Σy, h a = y), @sect _ _ _ s (λa, tr (mk a idp)) (sigma.pr1 z) =
                                    tr (fiber.mk a (sigma.pr2 z)))
               (@center_eq _ (is_contr_sigma_eq (h a)) (sigma.mk b p)),
      exact apd10 (@right_inverse _ _ _ s (λa, tr (fiber.mk a idp))) a
    end
  end
  end is_conn_map

  -- Connectedness is related to maps to and from the unit type, first to
  section
    parameters (n : trunc_index) (A : Type)

    definition is_conn_of_map_to_unit
      : is_conn_map n (λx : A, unit.star) → is_conn n A :=
    begin
      intro H, unfold is_conn_map at H,
      rewrite [-(ua (fiber.fiber_star_equiv A))],
      exact (H unit.star)
    end

    -- now maps from unit
    definition is_conn_of_map_from_unit (a₀ : A) (H : is_conn_map n (const unit a₀))
      : is_conn n .+1 A :=
    is_contr.mk (tr a₀)
    begin
      apply trunc.rec, intro a,
      exact trunc.elim (λz : fiber (const unit a₀) a, ap tr (point_eq z))
                            (@center _ (H a))
    end

    definition is_conn_map_from_unit (a₀ : A) [H : is_conn n .+1 A]
      : is_conn_map n (const unit a₀) :=
    begin
      intro a,
      apply is_conn_equiv_closed n (equiv.symm (fiber_const_equiv A a₀ a)),
      apply @is_contr_equiv_closed _ _ (tr_eq_tr_equiv n a₀ a),
    end

  end

  -- as special case we get elimination principles for pointed connected types
  namespace is_conn
    open pointed unit
    section
      parameters {n : trunc_index} {A : Type*}
                 [H : is_conn n .+1 A] (P : A → n-Type)

      include H
      protected definition rec : is_equiv (λs : Πa : A, P a, s (Point A)) :=
      @is_equiv_compose
        (Πa : A, P a) (unit → P (Point A)) (P (Point A))
        (λs x, s (Point A)) (λf, f unit.star)
        (is_conn_map.rec (is_conn_map_from_unit n A (Point A)) P)
        (to_is_equiv (unit.unit_imp_equiv (P (Point A))))

      protected definition elim : P (Point A) → (Πa : A, P a) :=
      @is_equiv.inv _ _ (λs, s (Point A)) rec

      protected definition elim_β (p : P (Point A)) : elim p (Point A) = p :=
      @is_equiv.right_inv _ _ (λs, s (Point A)) rec p
    end

    section
      parameters {n k : trunc_index} {A : Type*}
                 [H : is_conn n .+1 A] (P : A → (n +2+ k)-Type)

      include H
      proposition elim_general (p : P (Point A))
        : is_trunc k (fiber (λs : (Πa : A, P a), s (Point A)) p) :=
      @is_trunc_equiv_closed
        (fiber (λs x, s (Point A)) (λx, p))
        (fiber (λs, s (Point A)) p)
        k
        (equiv.symm (fiber.equiv_postcompose (to_fun (unit.unit_imp_equiv (P (Point A))))))
        (is_conn_map.elim_general (is_conn_map_from_unit n A (Point A)) P (λx, p))
    end
  end is_conn

  -- Lemma 7.5.2
  definition minus_one_conn_of_surjective {A B : Type} (f : A → B)
    : is_surjective f → is_conn_map -1 f :=
  begin
    intro H, intro b,
    exact @is_contr_of_inhabited_prop (∥fiber f b∥) (is_trunc_trunc -1 (fiber f b)) (H b),
  end

  definition is_surjection_of_minus_one_conn {A B : Type} (f : A → B)
    : is_conn_map -1 f → is_surjective f :=
  begin
    intro H, intro b,
    exact @center (∥fiber f b∥) (H b),
  end

  definition merely_of_minus_one_conn {A : Type} : is_conn -1 A → ∥A∥ :=
  λH, @center (∥A∥) H

  definition minus_one_conn_of_merely {A : Type} : ∥A∥ → is_conn -1 A :=
  @is_contr_of_inhabited_prop (∥A∥) (is_trunc_trunc -1 A)

  section
    open arrow

    variables {f g : arrow}

    -- Lemma 7.5.4
    definition retract_of_conn_is_conn [instance] (r : arrow_hom f g) [H : is_retraction r]
      (n : trunc_index) [K : is_conn_map n f] : is_conn_map n g :=
    begin
      intro b, unfold is_conn,
      apply is_contr_retract (trunc_functor n (retraction_on_fiber r b)),
      exact K (on_cod (arrow.is_retraction.sect r) b)
    end

  end

  -- Corollary 7.5.5
  definition is_conn_homotopy (n : trunc_index) {A B : Type} {f g : A → B}
    (p : f ~ g) (H : is_conn_map n f) : is_conn_map n g :=
  @retract_of_conn_is_conn _ _ (arrow.arrow_hom_of_homotopy p) (arrow.is_retraction_arrow_hom_of_homotopy p) n H

  -- all types are -2-connected
  definition minus_two_conn [instance] (A : Type) : is_conn -2 A :=
  _

  -- Theorem 8.2.1
  open susp

  definition is_conn_susp [instance] (n : trunc_index) (A : Type)
    [H : is_conn n A] : is_conn (n .+1) (susp A) :=
  is_contr.mk (tr north)
  begin
    apply trunc.rec,
    fapply susp.rec,
    { reflexivity },
    { exact (trunc.rec (λa, ap tr (merid a)) (center (trunc n A))) },
    { intro a,
      generalize (center (trunc n A)),
      apply trunc.rec,
      intro a',
      apply pathover_of_tr_eq,
      rewrite [transport_eq_Fr,idp_con],
      revert H, induction n with [n, IH],
      { intro H, apply is_prop.elim },
      { intros H,
        change ap (@tr n .+2 (susp A)) (merid a) = ap tr (merid a'),
        generalize a',
        apply is_conn_map.elim
              (is_conn_map_from_unit n A a)
              (λx : A, trunctype.mk' n (ap (@tr n .+2 (susp A)) (merid a) = ap tr (merid x))),
        intros,
        change ap (@tr n .+2 (susp A)) (merid a) = ap tr (merid a),
        reflexivity
      }
    }
  end

end homotopy
